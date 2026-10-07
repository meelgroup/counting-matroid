import CountingMatroid.Analysis.OutputSupport

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: The word-operation fold in `otherSteps` distributes over
two charged cost vectors. -/
theorem foldl_word_add (l : List Arlib.Computation.Op)
    (f g : Arlib.Computation.Op → ℕ) :
    ∀ a b, l.foldl (fun z x => z + (f x + g x)) (a + b) =
      l.foldl (fun z x => z + f x) a + l.foldl (fun z x => z + g x) b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro a b
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + f x) (b + g x)

/-- INTERNAL: Oracle charges add when charged computations are sequenced. -/
theorem oracleCalls_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    oracleCalls (p >>= f) = oracleCalls p + oracleCalls (f p.val) := by
  simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]

/-- INTERNAL: Nonoracle charges add when charged computations are sequenced. -/
theorem otherSteps_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    otherSteps (p >>= f) = otherSteps p + otherSteps (f p.val) := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := foldl_word_add Arlib.Computation.Op.all
    (fun x => p.cost (Op.word x)) (fun x => (f p.val).cost (Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega

/-- INTERNAL: A uniform per-iteration oracle bound controls a charged loop. -/
theorem oracleCalls_repeatFor_le {β : Type}
    {f : ℕ → β → Arlib.Computation.Charged Op Cell β} {k : ℕ}
    (h : ∀ j b, oracleCalls (f j b) ≤ k) (n : ℕ) (b : β) :
    oracleCalls (Arlib.Computation.Charged.repeatFor f n b) ≤ n * k := by
  have hfold : ∀ (l : List ℕ) (b : β),
      oracleCalls (Arlib.Computation.Charged.foldl (fun b j => f j b) l b) ≤
        l.length * k := by
    intro l
    induction l with
    | nil => intro b; simp [oracleCalls]
    | cons j js ih =>
        intro b
        have htail := ih (f j b).val
        have hhead := h j b
        simp only [List.length_cons]
        calc
          oracleCalls (Arlib.Computation.Charged.foldl
              (fun b j => f j b) (j :: js) b) =
              oracleCalls (f j b) +
                oracleCalls (Arlib.Computation.Charged.foldl
                  (fun b j => f j b) js (f j b).val) := by
                simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]
          _ ≤ k + js.length * k := Nat.add_le_add hhead htail
          _ = (js.length + 1) * k := by ring
  simpa [Arlib.Computation.Charged.repeatFor] using hfold (List.range n) b

/-- INTERNAL: A uniform per-element oracle bound controls a charged list scan. -/
theorem oracleCalls_foldl_le {β ι : Type}
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (k : ℕ)
    (h : ∀ b a, oracleCalls (f b a) ≤ k) :
    ∀ l b, oracleCalls (Arlib.Computation.Charged.foldl f l b) ≤ l.length * k := by
  intro l
  induction l with
  | nil => intro b; simp [oracleCalls]
  | cons a l ih =>
      intro b
      have ha := h b a
      have hr := ih (f b a).val
      simp only [List.length_cons]
      have hs : oracleCalls (Arlib.Computation.Charged.foldl f (a :: l) b) =
          oracleCalls (f b a) +
            oracleCalls (Arlib.Computation.Charged.foldl f l (f b a).val) := by
        simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]
      rw [hs]
      calc
        oracleCalls (f b a) + oracleCalls (Arlib.Computation.Charged.foldl f l (f b a).val)
            ≤ k + l.length * k := Nat.add_le_add ha hr
        _ = (l.length + 1) * k := by ring

/-- INTERNAL: A uniform per-iteration nonoracle bound controls a charged loop. -/
theorem otherSteps_repeatFor_le {β : Type}
    {f : ℕ → β → Arlib.Computation.Charged Op Cell β} {k : ℕ}
    (h : ∀ j b, otherSteps (f j b) ≤ k) (n : ℕ) (b : β) :
    otherSteps (Arlib.Computation.Charged.repeatFor f n b) ≤ n * k := by
  have hfold : ∀ (l : List ℕ) (b : β),
      otherSteps (Arlib.Computation.Charged.foldl (fun b j => f j b) l b) ≤
        l.length * k := by
    intro l
    induction l with
    | nil => intro b; simp [otherSteps]
    | cons j js ih =>
        intro b
        have htail := ih (f j b).val
        have hhead := h j b
        simp only [List.length_cons]
        have hsplit :
            otherSteps (Arlib.Computation.Charged.foldl
              (fun b j => f j b) (j :: js) b) =
              otherSteps (f j b) +
                otherSteps (Arlib.Computation.Charged.foldl
                  (fun b j => f j b) js (f j b).val) := by
          simp only [otherSteps, Arlib.Computation.Charged.cost_foldl_cons,
            Pi.add_apply]
          have hs := foldl_word_add Arlib.Computation.Op.all
            (fun x => (f j b).cost (Op.word x))
            (fun x => (Arlib.Computation.Charged.foldl
              (fun b j => f j b) js (f j b).val).cost (Op.word x)) 0 0
          simp only [Nat.zero_add] at hs
          rw [hs]
          omega
        calc
          otherSteps (Arlib.Computation.Charged.foldl
              (fun b j => f j b) (j :: js) b) =
              otherSteps (f j b) +
                otherSteps (Arlib.Computation.Charged.foldl
                  (fun b j => f j b) js (f j b).val) := hsplit
          _ ≤ k + js.length * k := Nat.add_le_add hhead htail
          _ = (js.length + 1) * k := by ring
  simpa [Arlib.Computation.Charged.repeatFor] using hfold (List.range n) b

/-- INTERNAL: The charged feasibility pretest contributes its contract bounds
and one comparison for the empty ground. -/
theorem preprocess_resource_bound (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) :
    oracleCalls (CountingMatroid.Program.preprocess contract.implementation n r o₁ o₂) ≤
      contract.callConstant * (n + r + 1) ^ contract.callDegree ∧
    otherSteps (CountingMatroid.Program.preprocess contract.implementation n r o₁ o₂) ≤
      contract.bitConstant * (n + r + 1) ^ contract.bitDegree + 1 := by
  have hsolver := contract.bounded n r o₁ o₂
  by_cases hn : n == 0
  · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn,
      oracleCalls, otherSteps,
      Arlib.Computation.Op.all, Arlib.Computation.CostVec.one]
  · by_cases hf : (contract.implementation.run n r o₁ o₂).val
    · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn, hf,
        oracleCalls, otherSteps,
        Arlib.Computation.Op.all, Arlib.Computation.CostVec.one] at *
      exact ⟨hsolver.1, by omega⟩
    · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn, hf,
        oracleCalls, otherSteps,
        Arlib.Computation.Op.all, Arlib.Computation.CostVec.one] at *
      exact ⟨hsolver.1, by omega⟩

/-- INTERNAL: Every early answer from the pretest is nonnegative. -/
theorem preprocess_answer_nonneg (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (h : (CountingMatroid.Program.preprocess contract.implementation n r o₁ o₂).val =
      some q) : 0 ≤ q := by
  by_cases hn : n == 0
  · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn] at h
    rw [h.symm]
    norm_num
  · by_cases hf : (contract.implementation.run n r o₁ o₂).val
    · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn, hf] at h
    · simp [CountingMatroid.Program.preprocess, inputSizeIsZero, hn, hf] at h
      rw [h.symm]

/-- INTERNAL: A greedy rank scan asks the supplied independence oracle at most
once per ground element.
TEXLINE: main.tex:1333-1346 -/
theorem greedyRank_oracleCalls_le {n : ℕ} (which : Bool)
    (oracle : IndependenceOracle n) (target : Finset (Fin n)) :
    oracleCalls (greedyRank which oracle target) ≤ n := by
  unfold greedyRank
  have hstep : ∀ (acc : Finset (Fin n) × ℕ) (i : Fin n),
      oracleCalls (do
        let present ← containsElement target i
        if present then
          let candidate ← insertElement acc.1 i
          let q ← encodeQuery candidate
          let independent ← oracleQuery which oracle q
          if independent then
            let size ← successor acc.2
            pure (candidate, size)
          else pure acc
        else pure acc) ≤ 1 := by
    intro acc i
    by_cases hi : i ∈ target
    · cases which <;>
        simp [containsElement, insertElement, encodeQuery, oracleQuery,
          successor, oracleCalls, hi] <;>
        split_ifs <;> simp_all
    · simp [containsElement, insertElement, encodeQuery, oracleQuery,
        successor, oracleCalls, hi]
  simpa [oracleCalls] using
    oracleCalls_foldl_le _ 1 hstep (List.finRange n)
      ((∅ : Finset (Fin n)), 0)

/-- INTERNAL: The paired-state projection scan makes no independence queries. -/
theorem pairedProjections_oracleCalls_zero {n : ℕ} (state : PairedSet n) :
    oracleCalls (pairedProjections state) = 0 := by
  unfold pairedProjections
  have hstep : ∀ (acc : Finset (Fin n) × Finset (Fin n) × ℕ) (i : Fin n),
      oracleCalls (do
        let inX ← containsPaired state (i, false)
        let x ← if inX then insertElement acc.1 i else pure acc.1
        let inY ← containsPaired state (i, true)
        if inY then
          let ysize ← successor acc.2.2
          pure (x, acc.2.1, ysize)
        else
          let complementY ← insertElement acc.2.1 i
          pure (x, complementY, acc.2.2)) ≤ 0 := by
    intro acc i
    by_cases hx : (i, false) ∈ state <;>
      by_cases hy : (i, true) ∈ state <;>
      simp [containsPaired, insertElement, successor, oracleCalls, hx, hy]
  have h := oracleCalls_foldl_le _ 0 hstep (List.finRange n)
    ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)
  simpa [oracleCalls] using Nat.eq_zero_of_le_zero h

/-- INTERNAL: The paired-rank formula makes at most two greedy scans.
TEXLINE: main.tex:1333-1346 -/
theorem pairedRank_oracleCalls_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (state : PairedSet n) :
    oracleCalls (pairedRank r o₁ o₂ state) ≤ 2 * n := by
  unfold pairedRank
  simp only [oracleCalls_bind]
  rw [pairedProjections_oracleCalls_zero]
  simp only [Nat.zero_add]
  have h₁ := greedyRank_oracleCalls_le false o₁ (pairedProjections state).val.1
  have h₂ := greedyRank_oracleCalls_le true o₂ (pairedProjections state).val.2.1
  simp [natAdd, natSub, oracleCalls] at *
  calc
    _ ≤ n + n := Nat.add_le_add h₁ h₂
    _ = 2 * n := by ring

/-- INTERNAL: Forming a rational power performs no independence queries. -/
theorem ratPower_oracleCalls_zero (q : ℚ) (exponent : ℕ) :
    oracleCalls (CountingMatroid.Program.ratPower q exponent) = 0 := by
  have h := oracleCalls_repeatFor_le (k := 0)
    (f := fun _ acc => ratMul acc q)
    (by intro _ _; simp [ratMul, oracleCalls]) exponent 1
  simpa [CountingMatroid.Program.ratPower] using Nat.eq_zero_of_le_zero h

/-- INTERNAL: Evaluating one paired-state weight uses at most one paired rank.
TEXLINE: main.tex:1380-1390 -/
theorem weightOfKind_oracleCalls_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (kind : StateKind n) :
    oracleCalls (CountingMatroid.Program.weightOfKind r o₁ o₂ q weights state kind) ≤
      2 * n := by
  cases kind with
  | invalid => simp [CountingMatroid.Program.weightOfKind, oracleCalls]
  | transversal =>
      have hp := ratPower_oracleCalls_zero q
        (n - (pairedRank r o₁ o₂ state).val)
      have hr := pairedRank_oracleCalls_le r o₁ o₂ state
      simp [CountingMatroid.Program.weightOfKind,
        natSub, oracleCalls] at hp hr ⊢
      omega
  | defect i j =>
      by_cases hij : i ≠ j
      · have hp := ratPower_oracleCalls_zero q
          (n - (pairedRank r o₁ o₂ state).val)
        have hr := pairedRank_oracleCalls_le r o₁ o₂ state
        simp [CountingMatroid.Program.weightOfKind, hij,
          natSub, multiplierRead, ratMul, oracleCalls] at hp hr ⊢
        omega
      · simp [CountingMatroid.Program.weightOfKind, hij, oracleCalls]

/-- PAPER: main.tex:1333-1440, 1455-1469
Every branch of the charged estimator, including abort branches, has a
nonnegative answer and polynomial charged costs. -/
theorem estimate_run_bound (contract : FeasibilityContract) :
    ∃ (C degree : ℕ), ∀ (n r : ℕ)
      (o₁ o₂ : IndependenceOracle n) (p : InputParams)
      (tape : ℕ → ℕ → Bool),
      r ≤ n →
      let run := CountingMatroid.Program.estimate contract.implementation
        n r o₁ o₂ p tape
      let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹)
      0 ≤ run.val ∧
      oracleCalls run ≤ C * (size + 1) ^ degree ∧
      otherSteps run ≤ C * (size + 1) ^ degree := by
  -- BLOCKER: `otherSteps` charges rational instructions by the squared bit
  -- length of their operands. A uniform `boundedRun` phase-body bound needs an
  -- invariant for the bit lengths of `currentWeights`, `product`, and the
  -- observation accumulator; the existing loop lemmas only compose such a
  -- bound after it is proved. Schedule and median costs remain to compose.
  sorry

/-- INTERNAL: A pointwise charged-run bound transfers to every supported
value of the output law. -/
theorem output_resource_bound (contract : FeasibilityContract) :
    ∃ (C degree : ℕ), ∀ (n r : ℕ)
      (o₁ o₂ : IndependenceOracle n) (p : InputParams),
      r ≤ n →
      let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹)
      ∀ x ∈ (Model.Run.outputLaw contract.implementation n r o₁ o₂ p).support,
        0 ≤ x.1 ∧
        x.2.oracleCalls ≤ C * (size + 1) ^ degree ∧
        x.2.bitOps ≤ C * (size + 1) ^ degree := by
  obtain ⟨C, degree, hbound⟩ := estimate_run_bound contract
  refine ⟨C, degree, ?_⟩
  intro n r o₁ o₂ p hr
  dsimp
  intro x hx
  obtain ⟨run, hrun, heq⟩ :=
    (OutputSupport.outputLaw_support_iff contract.implementation n r o₁ o₂ p x).mp hx
  obtain ⟨blocks, _, hblocks⟩ :=
    (OutputSupport.algorithmLaw_support_iff
      contract.implementation n r o₁ o₂ p run).mp hrun
  subst run
  subst x
  exact hbound n r o₁ o₂ p (Model.Run.blockTape blocks) hr

end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · open · proved greedy and paired rank oracle caps and zero oracle cost of rational powers; the annealing phase still needs rational-size invariants.
* r2 · open · proved charged bind/loop and pretest resource lemmas; the annealing phase bound still needs rational-size invariants.
* r1 · open · proved support transport and added `r ≤ n`; the per-run charged polynomial bound remains unproved.
-/
