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

/-- INTERNAL: The charged power loop computes ordinary rational exponentiation.
TEXLINE: main.tex:1386-1390 -/
theorem ratPower_val_eq (q : ℚ) (exponent : ℕ) :
    (CountingMatroid.Program.ratPower q exponent).val = q ^ exponent := by
  have hfold : ∀ (l : List ℕ) (acc : ℚ),
      (Arlib.Computation.Charged.foldl (fun acc _ => ratMul acc q) l acc).val =
        acc * q ^ l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons _ l ih =>
        intro acc
        simp only [Arlib.Computation.Charged.val_foldl_cons, List.length_cons]
        rw [ih]
        simp [ratMul, pow_succ]
        ring
  unfold CountingMatroid.Program.ratPower Arlib.Computation.Charged.repeatFor
  simpa using hfold (List.range exponent) 1

/-- INTERNAL: Nonnegative phase weights remain nonnegative through the charged
power loop. TEXLINE: main.tex:1386-1390 -/
theorem ratPower_val_nonneg (q : ℚ) (exponent : ℕ) (hq : 0 ≤ q) :
    0 ≤ (CountingMatroid.Program.ratPower q exponent).val := by
  rw [ratPower_val_eq]
  positivity

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

/-- INTERNAL: Classifying a paired state does not query either oracle.
TEXLINE: main.tex:1333-1346 -/
theorem classifyState_oracleCalls_zero {n : ℕ} (state : PairedSet n) :
    oracleCalls (CountingMatroid.Program.classifyState state) = 0 := by
  unfold CountingMatroid.Program.classifyState
  have hstep : ∀ (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n),
      oracleCalls (do
        let x ← containsPaired state (i, false)
        let y ← containsPaired state (i, true)
        if x then
          if y then
            let seen ← isSome acc.2.1
            if seen then pure (acc.1, acc.2.1, true)
            else pure (acc.1, some i, acc.2.2)
          else pure acc
        else
          if y then pure acc
          else
            let seen ← isSome acc.1
            if seen then pure (acc.1, acc.2.1, true)
            else pure (some i, acc.2.1, acc.2.2)) ≤ 0 := by
    intro acc i
    rcases acc with ⟨a, b, c⟩
    cases a <;> cases b <;>
      by_cases hx : (i, false) ∈ state <;>
      by_cases hy : (i, true) ∈ state <;>
      simp [containsPaired, isSome, oracleCalls, hx, hy]
  have h := oracleCalls_foldl_le _ 0 hstep (List.finRange n)
    ((none : Option (Fin n)), (none : Option (Fin n)), false)
  have hz : oracleCalls (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (Fin n)), (none : Option (Fin n)), false)) = 0 :=
    Nat.eq_zero_of_le_zero (by simpa using h)
  simp only [oracleCalls_bind]
  rw [hz]
  simp only [Nat.zero_add]
  split_ifs
  · simp [oracleCalls]
  · rename_i hnot
    cases h₁ : (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (Fin n)), (none : Option (Fin n)), false)).val.1 <;>
    cases h₂ : (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (Fin n)), (none : Option (Fin n)), false)).val.2.1 <;>
    simp [indexEqual, oracleCalls]
    case neg.some.some x y =>
      by_cases hxy : x = y <;> simp [hxy]

/-- INTERNAL: Recording an observation performs at most one paired-rank scan.
TEXLINE: main.tex:1333-1346 -/
theorem recordObservation_oracleCalls_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ)
    (current : CountingMatroid.Program.ObservationCursor n) :
    oracleCalls (CountingMatroid.Program.recordObservation r o₁ o₂ rho current) ≤
      2 * n := by
  unfold CountingMatroid.Program.recordObservation
  simp only [oracleCalls_bind]
  rw [classifyState_oracleCalls_zero]
  simp only [Nat.zero_add]
  cases hkind : (CountingMatroid.Program.classifyState current.state).val with
  | invalid => simp [oracleCalls]
  | defect i j => simp [countIncrement, oracleCalls]
  | transversal =>
      have hr := pairedRank_oracleCalls_le r o₁ o₂ current.state
      have hp := ratPower_oracleCalls_zero rho
        (n - (pairedRank r o₁ o₂ current.state).val)
      simp [countIncrement, natSub, ratAdd, oracleCalls] at hr hp ⊢
      omega

/-- INTERNAL: A capped integer draw only reads fair bits and uses word operations.
TEXLINE: main.tex:1392-1421 -/
theorem boundedUniform_oracleCalls_zero (tape : ℕ → Bool)
    (trials v cursor : ℕ) :
    oracleCalls (CountingMatroid.Program.boundedUniform tape trials v cursor) = 0 := by
  have hbits (width start : ℕ) :
      oracleCalls (Arlib.Computation.Charged.repeatFor
        (fun _ inner => do
          let bit ← fairBit tape inner.2
          let value ← appendBit inner.1 bit
          Prod.mk value <$> successor inner.2) width (0, start)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply oracleCalls_repeatFor_le (k := 0)
    intro _ _
    simp [fairBit, appendBit, successor, oracleCalls]
  have htrials (width : ℕ) : ∀ acc,
      oracleCalls (do
        let done ← isSome acc.1
        if done then pure acc
        else
          let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
            let bit ← fairBit tape inner.2
            let value ← appendBit inner.1 bit
            let next ← successor inner.2
            pure (value, next)) width (0, acc.2)
          let accepted ← lessThan trial.1 v
          if accepted then pure (some trial.1, trial.2)
          else pure (none, trial.2)) = 0 := by
    intro acc
    by_cases hd : acc.1.isSome
    · simp [isSome, hd, oracleCalls]
    · simp [isSome, hd, oracleCalls_bind]
      refine ⟨by simp [oracleCalls], hbits width acc.2,
        by simp [lessThan, oracleCalls], ?_⟩
      split_ifs <;> simp [oracleCalls]
  unfold CountingMatroid.Program.boundedUniform
  by_cases hv : v < 1
  · simp [lessThan, hv, oracleCalls]
  · by_cases hs : v < 2
    · simp [lessThan, hv, hs, oracleCalls]
    · have hloop := oracleCalls_repeatFor_le (k := 0)
        (f := fun _ acc => do
          let done ← isSome acc.1
          if done then pure acc
          else
            let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
              let bit ← fairBit tape inner.2
              let value ← appendBit inner.1 bit
              let next ← successor inner.2
              pure (value, next)) ((v - 1).log2 + 1) (0, acc.2)
            let accepted ← lessThan trial.1 v
            if accepted then pure (some trial.1, trial.2)
            else pure (none, trial.2))
        (by intro _ acc; exact le_of_eq (htrials _ acc))
        trials ((none : Option ℕ), cursor)
      simp [lessThan, hv, hs, uniformWidth, oracleCalls] at hloop ⊢
      omega

/-- INTERNAL: Visiting a paired label to select an occupied or free element
does not query an independence oracle. -/
theorem selectionVisit_oracleCalls_zero {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ)
    (acc : Option (PairedGround n) × ℕ) (element : PairedGround n) :
    oracleCalls (CountingMatroid.Program.selectionVisit state occupied k acc element) =
      0 := by
  unfold CountingMatroid.Program.selectionVisit
  cases occupied <;>
    by_cases hi : element ∈ state <;>
    by_cases hk : acc.2 = k <;>
    simp [containsPaired, natEqual, successor, oracleCalls, hi, hk]

/-- INTERNAL: Both scans in a paired-label selection use only word operations. -/
theorem selectPaired_oracleCalls_zero {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) :
    oracleCalls (CountingMatroid.Program.selectPaired state occupied k) = 0 := by
  unfold CountingMatroid.Program.selectPaired
  have hinner : ∀ (acc : Option (PairedGround n) × ℕ) (i : Fin n),
      oracleCalls (Arlib.Computation.Charged.foldl
        (CountingMatroid.Program.selectionVisit state occupied k)
        [((i, false) : PairedGround n), (i, true)] acc) ≤ 0 := by
    intro acc i
    have h := oracleCalls_foldl_le _ 0
      (by intro b a; exact Nat.le_zero.mpr (selectionVisit_oracleCalls_zero state occupied k b a))
      [((i, false) : PairedGround n), (i, true)] acc
    simpa using h
  have h := oracleCalls_foldl_le _ 0 hinner (List.finRange n)
    ((none : Option (PairedGround n)), 0)
  have hz : oracleCalls (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (PairedGround n)), 0)) = 0 :=
    Nat.eq_zero_of_le_zero (by simpa using h)
  simp only [oracleCalls_bind]
  rw [hz]
  simp [oracleCalls]

/-- INTERNAL: The rational acceptance comparison uses no independence query.
TEXLINE: main.tex:1392-1421 -/
theorem acceptance_oracleCalls_zero {n : ℕ} (tape : ℕ → Bool)
    (drawTrials : ℕ) (oldWeight newWeight : ℚ)
    (state candidate : PairedSet n) (cursor : ℕ) :
    oracleCalls (do
      let ratio ← ratDiv newWeight oldWeight
      let needsDraw ← ratLess ratio 1
      if needsDraw then
        let denominator ← rationalDenominator ratio
        let numerator ← rationalNumerator ratio
        let acceptedDraw ← CountingMatroid.Program.boundedUniform tape drawTrials
          denominator cursor
        match acceptedDraw.1 with
        | none => pure none
        | some value =>
            let accepted ← lessThan value numerator
            if accepted then pure (some (candidate, acceptedDraw.2))
            else pure (some (state, acceptedDraw.2))
      else pure (some (candidate, cursor))) = 0 := by
  simp only [oracleCalls_bind]
  have hdiv : oracleCalls (ratDiv newWeight oldWeight) = 0 := by
    simp [ratDiv, oracleCalls]
  have hless : ∀ a b : ℚ, oracleCalls (ratLess a b) = 0 := by
    intro a b
    simp [ratLess, oracleCalls]
  have hden : ∀ a : ℚ, oracleCalls (rationalDenominator a) = 0 := by
    intro a
    simp [rationalDenominator, oracleCalls]
  have hnum : ∀ a : ℚ, oracleCalls (rationalNumerator a) = 0 := by
    intro a
    simp [rationalNumerator, oracleCalls]
  simp only [hdiv, hless, Nat.zero_add]
  split_ifs
  · simp only [oracleCalls_bind]
    simp only [hden, hnum, Nat.zero_add]
    rw [boundedUniform_oracleCalls_zero]
    simp only [Nat.zero_add]
    split
    · simp [oracleCalls]
    · simp [lessThan, oracleCalls]
      split_ifs <;> simp
  · simp [oracleCalls]

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
  -- length of their operands. A uniform `boundedRun` phase-body bound needs
  -- all of the following through the nested phase, restart, and observation
  -- loops: each learned multiplier has bit length bounded by its number of
  -- updates times the count length; each observation accumulator has bit
  -- length bounded by its observation count times the `rho`-power length;
  -- and `product` has bit length bounded by the sum of completed ratio lengths.
  -- The loop cost lemmas only compose a bound once these invariants hold.
  -- Schedule, uniform-draw, and median bit costs remain to compose.
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

* r5 · open · proved charged rational-power value and nonnegativity, and zero oracle calls for rational acceptance; the full polynomial bound still needs rational-size invariants.
* r4 · open · proved zero oracle cost for classification, bounded uniform draws, and paired selection, plus a `2*n` oracle cap for observation recording; rational-size invariants still block the full run bound.
* r3 · open · proved greedy and paired rank oracle caps and zero oracle cost of rational powers; the annealing phase still needs rational-size invariants.
* r2 · open · proved charged bind/loop and pretest resource lemmas; the annealing phase bound still needs rational-size invariants.
* r1 · open · proved support transport and added `r ≤ n`; the per-run charged polynomial bound remains unproved.
-/
