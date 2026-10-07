import CountingMatroid.Analysis.OutputSupport
import CountingMatroid.Analysis.BoundedRunResourceEnvelope
import CountingMatroid.Analysis.ScheduleResourceEnvelope
import CountingMatroid.Analysis.SortedInsertValue
import CountingMatroid.Analysis.EstimateMedianResource

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: Oracle charges add when charged computations are sequenced. -/
theorem oracleCalls_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    oracleCalls (p >>= f) = oracleCalls p + oracleCalls (f p.val) := by
  simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]

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

/-- INTERNAL: Sorting a rational list uses no independence-oracle queries. -/
theorem sortedInsert_oracleCalls_zero (value : ℚ) (sorted : List ℚ) :
    oracleCalls (CountingMatroid.Program.sortedInsert value sorted) = 0 := by
  let step : List ℚ × Bool → ℚ → Arlib.Computation.Charged Op Cell (List ℚ × Bool) :=
    fun acc item => do
      if acc.2 then
        let reversed ← consRational item acc.1
        pure (reversed, true)
      else
        let before ← ratLess value item
        if before then
          let reversed ← consRational value acc.1
          let reversed ← consRational item reversed
          pure (reversed, true)
        else
          let reversed ← consRational item acc.1
          pure (reversed, false)
  have hstep (acc : List ℚ × Bool) (item : ℚ) :
      oracleCalls (step acc item) ≤ 0 := by
    rcases acc with ⟨rev, flag⟩
    cases flag <;>
      simp [step, ratLess, consRational, oracleCalls] <;>
      split_ifs <;> simp [oracleCalls]
  have hfold := oracleCalls_foldl_le step 0 hstep sorted (([] : List ℚ), false)
  unfold CountingMatroid.Program.sortedInsert
  change oracleCalls (do
    let (reversed, inserted) ← Arlib.Computation.Charged.foldl step sorted ([], false)
    let reversed ← if inserted then pure reversed else consRational value reversed
    reverseRationals reversed) = 0
  simp only [oracleCalls_bind]
  have hzero : oracleCalls (Arlib.Computation.Charged.foldl step sorted ([], false)) = 0 := by
    simpa using hfold
  rw [hzero]
  cases (Arlib.Computation.Charged.foldl step sorted ([], false)).val.2 <;>
    simp [consRational, reverseRationals, oracleCalls]

/-- INTERNAL: The complete charged median scan makes no independence query. -/
theorem medianRational_oracleCalls_zero (values : List ℚ) :
    oracleCalls (CountingMatroid.Program.medianRational values) = 0 := by
  unfold CountingMatroid.Program.medianRational
  simp only [oracleCalls_bind]
  have hfold : ∀ (l acc : List ℚ),
      oracleCalls (Arlib.Computation.Charged.foldl
        (fun acc value => CountingMatroid.Program.sortedInsert value acc) l acc) = 0 := by
    intro l
    induction l with
    | nil => intro acc; simp [oracleCalls]
    | cons value l ih =>
        intro acc
        change oracleCalls (CountingMatroid.Program.sortedInsert value acc >>=
          fun next => Arlib.Computation.Charged.foldl
            (fun acc value => CountingMatroid.Program.sortedInsert value acc) l next) = 0
        rw [oracleCalls_bind, sortedInsert_oracleCalls_zero, ih]
  rw [hfold values []]
  simp [halfNat, nthRational, oracleCalls]

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

/-- INTERNAL: The schedule envelope supplies the sign condition required by
the capped-run envelope. This is the nonnegative bounded-run output that the
estimator's median step will consume.
TEXLINE: main.tex:1350-1440 -/
theorem scheduled_boundedRun_nonneg (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → Bool) :
    0 ≤ (CountingMatroid.Program.boundedRun r o₁ o₂ tape
      (CountingMatroid.Program.schedule n p).val 0).val.1 := by
  obtain ⟨_, _, hschedule⟩ :=
    ScheduleResourceEnvelope.schedule_resource_envelope
  obtain ⟨_, _, hrun⟩ :=
    BoundedRunResourceEnvelope.boundedRun_resource_envelope
  exact (hrun n r o₁ o₂ tape (CountingMatroid.Program.schedule n p).val
    (hschedule n r p).1).1

/-- INTERNAL: Every observation in the estimator's median list is
nonnegative on the branch that enters annealing.
TEXLINE: main.tex:1430-1440 -/
theorem estimate_none_nonneg (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = none) :
    0 ≤ (CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape).val := by
  let s := (CountingMatroid.Program.schedule n p).val
  have hstep (j : ℕ) (acc : List ℚ) (hacc : ∀ q ∈ acc, 0 ≤ q) :
      ∀ q ∈ (do
        let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂
          (tape j) s 0
        consRational value acc).val, 0 ≤ q := by
    intro q hq
    simp only [Arlib.Computation.Charged.val_bind, consRational,
      Arlib.Computation.Charged.val_op] at hq
    rcases List.mem_cons.mp hq with rfl | hq
    · exact scheduled_boundedRun_nonneg n r o₁ o₂ p (tape j)
    · exact hacc q hq
  have hloop : ∀ (l : List ℕ) (acc : List ℚ),
      (∀ q ∈ acc, 0 ≤ q) →
      ∀ q ∈ (Arlib.Computation.Charged.foldl
        (fun acc j => do
          let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂
            (tape j) s 0
          consRational value acc) l acc).val, 0 ≤ q := by
    intro l
    induction l with
    | nil => intro acc hacc q hq; exact hacc q hq
    | cons j js ih =>
        intro acc hacc q hq
        rw [Arlib.Computation.Charged.val_foldl_cons] at hq
        exact ih _ (hstep j acc hacc) q hq
  have hmed := medianRational_nonneg
    (Arlib.Computation.Charged.repeatFor
      (fun j acc => do
        let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂
          (tape j) s 0
        consRational value acc) s.repetitions ([] : List ℚ)).val
    (by simpa [Arlib.Computation.Charged.repeatFor] using
      hloop (List.range s.repetitions) [] (by simp))
  simpa [CountingMatroid.Program.estimate, h, s] using hmed

/-- INTERNAL: Once every bounded run has a common charge and output-length
bound, the estimator's annealing branch has an explicit finite cost bound.
TEXLINE: main.tex:1430-1440 -/
theorem estimate_none_raw_cost_bound (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (K : ℕ)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = none)
    (hrun : ∀ j,
      let run := CountingMatroid.Program.boundedRun r o₁ o₂ (tape j)
        (CountingMatroid.Program.schedule n p).val 0
      binaryRatLength run.val.1 ≤ K ∧
      oracleCalls run ≤ K ∧ otherSteps run ≤ K) :
    let pre := CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂
    let schedule := CountingMatroid.Program.schedule n p
    let T := schedule.val.repetitions
    let run := CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape
    oracleCalls run ≤ oracleCalls pre + oracleCalls schedule + T * K ∧
    otherSteps run ≤ otherSteps pre + otherSteps schedule + T * (K + 1) +
      (T + 1) ^ 2 * (2 * K + 8) := by
  let pre := CountingMatroid.Program.preprocess contract.implementation n r o₁ o₂
  let schedule := CountingMatroid.Program.schedule n p
  let s := schedule.val
  let step : ℕ → List ℚ → Arlib.Computation.Charged Op Cell (List ℚ) :=
    fun j acc => do
      let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0
      consRational value acc
  let loop := Arlib.Computation.Charged.repeatFor step s.repetitions ([] : List ℚ)
  have hstepCalls (j : ℕ) (acc : List ℚ) : oracleCalls (step j acc) ≤ K := by
    have hj := (hrun j).2.1
    simpa [step, oracleCalls_bind, consRational, oracleCalls, s, schedule] using hj
  have hstepSteps (j : ℕ) (acc : List ℚ) : otherSteps (step j acc) ≤ K + 1 := by
    have hj := (hrun j).2.2
    have hcost : otherSteps (step j acc) =
        otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0) + 1 := by
      simp [step, otherSteps_bind, consRational, otherSteps,
        Arlib.Computation.Op.all]
      omega
    rw [hcost]
    simpa [s, schedule] using Nat.add_le_add_right hj 1
  have hloopCalls : oracleCalls loop ≤ s.repetitions * K :=
    oracleCalls_repeatFor_le (f := step) (k := K) hstepCalls s.repetitions []
  have hloopSteps : otherSteps loop ≤ s.repetitions * (K + 1) :=
    otherSteps_repeatFor_le (f := step) (k := K + 1)
      hstepSteps s.repetitions []
  have hloopSize : loop.val.length = s.repetitions ∧
      ∀ q ∈ loop.val, binaryRatLength q ≤ K := by
    have hfold : ∀ (l : List ℕ) (acc : List ℚ),
        (∀ q ∈ acc, binaryRatLength q ≤ K) →
        let out := (Arlib.Computation.Charged.foldl
          (fun acc j => step j acc) l acc).val
        out.length = acc.length + l.length ∧
          ∀ q ∈ out, binaryRatLength q ≤ K := by
      intro l
      induction l with
      | nil => intro acc hacc; exact ⟨by simp, hacc⟩
      | cons j js ih =>
          intro acc hacc
          have hval : (step j acc).val =
              (CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0).val.1 :: acc := by
            simp [step, consRational]
          have hnext : ∀ q ∈ (step j acc).val,
              binaryRatLength q ≤ K := by
            rw [hval]
            intro q hq
            rcases List.mem_cons.mp hq with rfl | hq
            · exact (hrun j).1
            · exact hacc q hq
          have htail := ih (step j acc).val hnext
          simpa [Arlib.Computation.Charged.val_foldl_cons, hval,
            Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail
    simpa [loop, Arlib.Computation.Charged.repeatFor] using
      hfold (List.range s.repetitions) [] (by simp)
  have hmedianCalls : oracleCalls (CountingMatroid.Program.medianRational loop.val) = 0 :=
    medianRational_oracleCalls_zero loop.val
  have hmedianSteps : otherSteps (CountingMatroid.Program.medianRational loop.val) ≤
      (s.repetitions + 1) ^ 2 * (2 * K + 8) := by
    rw [← hloopSize.1]
    exact medianRational_otherSteps_le loop.val K hloopSize.2
  change oracleCalls (CountingMatroid.Program.estimate
      contract.implementation n r o₁ o₂ p tape) ≤
      oracleCalls pre + oracleCalls schedule + s.repetitions * K ∧
    otherSteps (CountingMatroid.Program.estimate
      contract.implementation n r o₁ o₂ p tape) ≤
      otherSteps pre + otherSteps schedule + s.repetitions * (K + 1) +
        (s.repetitions + 1) ^ 2 * (2 * K + 8)
  have hsplitCalls : oracleCalls (CountingMatroid.Program.estimate
      contract.implementation n r o₁ o₂ p tape) =
      oracleCalls pre + oracleCalls schedule + oracleCalls loop +
        oracleCalls (CountingMatroid.Program.medianRational loop.val) := by
    simp [CountingMatroid.Program.estimate, h, oracleCalls_bind,
      pre, schedule, s, loop, step, Nat.add_assoc]
  have hsplitSteps : otherSteps (CountingMatroid.Program.estimate
      contract.implementation n r o₁ o₂ p tape) =
      otherSteps pre + otherSteps schedule + otherSteps loop +
        otherSteps (CountingMatroid.Program.medianRational loop.val) := by
    simp [CountingMatroid.Program.estimate, h, otherSteps_bind,
      pre, schedule, s, loop, step, Nat.add_assoc]
  constructor
  · rw [hsplitCalls, hmedianCalls]
    omega
  · rw [hsplitSteps]
    omega

/-- INTERNAL: An early pretest answer is the estimator's answer, and the
estimator incurs exactly the pretest charges on that branch.
TEXLINE: main.tex:1442-1469 -/
theorem estimate_preliminary_branch (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (q : ℚ)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = some q) :
    let pre := CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂
    let run := CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape
    run.val = q ∧ oracleCalls run = oracleCalls pre ∧
      otherSteps run = otherSteps pre := by
  dsimp
  simp [CountingMatroid.Program.estimate, h, oracleCalls, otherSteps]

/-- INTERNAL: The early-answer branch already satisfies the pretest's exact
resource bounds and answer sign, independently of schedule construction.
TEXLINE: main.tex:1442-1469 -/
theorem estimate_preliminary_resource_bound (contract : FeasibilityContract)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (q : ℚ)
    (h : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = some q) :
    let run := CountingMatroid.Program.estimate contract.implementation
      n r o₁ o₂ p tape
    0 ≤ run.val ∧
    oracleCalls run ≤ contract.callConstant * (n + r + 1) ^ contract.callDegree ∧
    otherSteps run ≤
      contract.bitConstant * (n + r + 1) ^ contract.bitDegree + 1 := by
  obtain ⟨hval, hcalls, hsteps⟩ :=
    estimate_preliminary_branch contract n r o₁ o₂ p tape q h
  obtain ⟨hpreCalls, hpreSteps⟩ :=
    preprocess_resource_bound contract n r o₁ o₂
  dsimp at *
  rw [hval, hcalls, hsteps]
  exact ⟨preprocess_answer_nonneg contract n r o₁ o₂ q h,
    hpreCalls, hpreSteps⟩

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
  have hnone : ∃ (C degree : ℕ), ∀ (n r : ℕ)
      (o₁ o₂ : IndependenceOracle n) (p : InputParams)
      (tape : ℕ → ℕ → Bool), r ≤ n →
      (CountingMatroid.Program.preprocess contract.implementation
        n r o₁ o₂).val = none →
      let run := CountingMatroid.Program.estimate contract.implementation
        n r o₁ o₂ p tape
      let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹)
      0 ≤ run.val ∧
      oracleCalls run ≤ C * (size + 1) ^ degree ∧
      otherSteps run ≤ C * (size + 1) ^ degree := by
    have hcost : ∃ (C degree : ℕ), ∀ (n r : ℕ)
        (o₁ o₂ : IndependenceOracle n) (p : InputParams)
        (tape : ℕ → ℕ → Bool), r ≤ n →
        (CountingMatroid.Program.preprocess contract.implementation
          n r o₁ o₂).val = none →
        let run := CountingMatroid.Program.estimate contract.implementation
          n r o₁ o₂ p tape
        let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹)
        oracleCalls run ≤ C * (size + 1) ^ degree ∧
        otherSteps run ≤ C * (size + 1) ^ degree := by
      obtain ⟨Cs, Ds, hschedule⟩ :=
        ScheduleResourceEnvelope.schedule_resource_envelope
      obtain ⟨Cr, Dr, hbounded⟩ :=
        BoundedRunResourceEnvelope.boundedRun_resource_envelope
      let A := Cs + Cr + contract.callConstant * 2 ^ contract.callDegree +
        contract.bitConstant * 2 ^ contract.bitDegree + 10
      let D := Ds + Dr + contract.callDegree + contract.bitDegree + 10
      refine ⟨100 * A ^ (Dr + 4), D * (Dr + 4), ?_⟩
      intro n r o₁ o₂ p tape hr hpre
      let X := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let s := (CountingMatroid.Program.schedule n p).val
      let B := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      let R := Cr * B ^ Dr
      have hs := hschedule n r p
      have hrun (j : ℕ) :
          let run := CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0
          binaryRatLength run.val.1 ≤ R ∧
            oracleCalls run ≤ R ∧ otherSteps run ≤ R := by
        simpa [R, B, s] using
          (hbounded n r o₁ o₂ (tape j) s hs.1).2
      have hraw := estimate_none_raw_cost_bound contract n r o₁ o₂ p tape R
        hpre (by simpa [R, s] using hrun)
      let Q := A * X ^ D
      have hX : 1 ≤ X := by dsimp [X]; omega
      have hA : 10 ≤ A := by dsimp [A]; omega
      have hQ : 1 ≤ Q := by
        dsimp [Q]
        have hp : 1 ≤ X ^ D := one_le_pow₀ hX
        nlinarith
      have hbase : Cs * X ^ Ds ≤ Q := by
        dsimp [Q]
        exact Nat.mul_le_mul (by dsimp [A]; omega)
          (pow_le_pow_right₀ hX (by dsimp [D]; omega))
      have hB : B ≤ Q := by
        have hh := hs.2.1
        have hpart : B ≤ Cs * X ^ Ds := by
          dsimp [B, s, X] at hh ⊢
          omega
        exact le_trans hpart hbase
      have hT : s.repetitions ≤ Q := by
        have hh := hs.2.1
        dsimp [s, X] at *
        omega
      have hscheduleCalls : oracleCalls (CountingMatroid.Program.schedule n p) ≤ Q := by
        exact le_trans hs.2.2.1 hbase
      have hscheduleSteps : otherSteps (CountingMatroid.Program.schedule n p) ≤ Q := by
        exact le_trans hs.2.2.2 hbase
      have hpreBounds := preprocess_resource_bound contract n r o₁ o₂
      have h2X : n + r + 1 ≤ 2 * X := by dsimp [X]; omega
      have hpreCalls : oracleCalls (CountingMatroid.Program.preprocess
          contract.implementation n r o₁ o₂) ≤ Q := by
        calc
          _ ≤ contract.callConstant * (n + r + 1) ^ contract.callDegree :=
            hpreBounds.1
          _ ≤ contract.callConstant * (2 * X) ^ contract.callDegree :=
            Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h2X _)
          _ = (contract.callConstant * 2 ^ contract.callDegree) *
              X ^ contract.callDegree := by rw [mul_pow]; ring
          _ ≤ Q := by
            dsimp [Q]
            exact Nat.mul_le_mul (by dsimp [A]; omega)
              (pow_le_pow_right₀ hX (by dsimp [D]; omega))
      have hpreSteps : otherSteps (CountingMatroid.Program.preprocess
          contract.implementation n r o₁ o₂) ≤ Q := by
        have hpow := Nat.pow_le_pow_left h2X contract.bitDegree
        have hcoeff : contract.bitConstant * (n + r + 1) ^
            contract.bitDegree + 1 ≤
            (contract.bitConstant * 2 ^ contract.bitDegree + 1) *
              X ^ contract.bitDegree := by
          have hp : 1 ≤ X ^ contract.bitDegree := one_le_pow₀ hX
          calc
            _ ≤ contract.bitConstant * (2 * X) ^ contract.bitDegree + 1 :=
              Nat.add_le_add_right (Nat.mul_le_mul_left _ hpow) 1
            _ = (contract.bitConstant * 2 ^ contract.bitDegree) *
                X ^ contract.bitDegree + 1 := by rw [mul_pow]; ring
            _ ≤ (contract.bitConstant * 2 ^ contract.bitDegree + 1) *
                X ^ contract.bitDegree := by nlinarith
        exact le_trans hpreBounds.2 (le_trans hcoeff (by
          dsimp [Q]
          exact Nat.mul_le_mul (by dsimp [A]; omega)
            (pow_le_pow_right₀ hX (by dsimp [D]; omega))))
      have hCr : Cr ≤ Q := by
        have hp : 1 ≤ X ^ D := one_le_pow₀ hX
        calc
          Cr ≤ A := by dsimp [A]; omega
          _ = A * 1 := by omega
          _ ≤ Q := by
            dsimp [Q]
            exact Nat.mul_le_mul_left A hp
      have hR : R ≤ Q ^ (Dr + 1) := by
        calc
          R = Cr * B ^ Dr := rfl
          _ ≤ Q * Q ^ Dr := Nat.mul_le_mul hCr
            (Nat.pow_le_pow_left hB Dr)
          _ = Q ^ (Dr + 1) := by rw [pow_succ]; ac_rfl
      let a := Q ^ (Dr + 1)
      let P := Q ^ (Dr + 4)
      have ha : 1 ≤ a := one_le_pow₀ hQ
      have hQP : Q ≤ P := by
        simpa [P, pow_one] using
          (pow_le_pow_right₀ hQ (by omega : 1 ≤ Dr + 4))
      have hQaP : Q * a ≤ P := by
        calc
          Q * a = Q ^ 1 * Q ^ (Dr + 1) := by simp [a]
          _ = Q ^ (1 + (Dr + 1)) := (pow_add Q 1 (Dr + 1)).symm
          _ = Q ^ (Dr + 2) := by congr 1; omega
          _ ≤ P := pow_le_pow_right₀ hQ (by omega)
      have hQ2aP : Q ^ 2 * a ≤ P := by
        calc
          Q ^ 2 * a = Q ^ 2 * Q ^ (Dr + 1) := rfl
          _ = Q ^ (2 + (Dr + 1)) := (pow_add Q 2 (Dr + 1)).symm
          _ = Q ^ (Dr + 3) := by congr 1; omega
          _ ≤ P := pow_le_pow_right₀ hQ (by omega)
      have hTplus : s.repetitions + 1 ≤ 2 * Q := by omega
      have hTplusSq : (s.repetitions + 1) ^ 2 ≤ 4 * Q ^ 2 := by
        calc
          _ ≤ (2 * Q) ^ 2 := Nat.pow_le_pow_left hTplus 2
          _ = 4 * Q ^ 2 := by
            rw [mul_pow]
            norm_num
      have hRplus : 2 * R + 8 ≤ 10 * a := by
        have hh : R ≤ a := hR
        omega
      have hmedian : (s.repetitions + 1) ^ 2 * (2 * R + 8) ≤
          40 * P := by
        calc
          _ ≤ (4 * Q ^ 2) * (10 * a) :=
            Nat.mul_le_mul hTplusSq hRplus
          _ = 40 * (Q ^ 2 * a) := by
            simpa only [show (4 : ℕ) * 10 = 40 by norm_num] using
              (mul_mul_mul_comm (4 : ℕ) (Q ^ 2) 10 a)
          _ ≤ 40 * P := Nat.mul_le_mul_left 40 hQ2aP
      have hTR : s.repetitions * R ≤ P :=
        le_trans (Nat.mul_le_mul hT hR) hQaP
      have hTR1 : s.repetitions * (R + 1) ≤ 2 * P := by
        have hRa : R + 1 ≤ 2 * a := by omega
        calc
          _ ≤ Q * (2 * a) := Nat.mul_le_mul hT hRa
          _ = 2 * (Q * a) := by
            calc
              Q * (2 * a) = (Q * 2) * a := (mul_assoc Q 2 a).symm
              _ = (2 * Q) * a := by rw [mul_comm Q 2]
              _ = 2 * (Q * a) := mul_assoc 2 Q a
          _ ≤ 2 * P := Nat.mul_le_mul_left 2 hQaP
      have hrawCalls := hraw.1
      have hrawSteps := hraw.2
      have hfinalCalls : oracleCalls (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤ 100 * P := by
        calc
          _ ≤ oracleCalls (CountingMatroid.Program.preprocess
                contract.implementation n r o₁ o₂) +
              oracleCalls (CountingMatroid.Program.schedule n p) +
              s.repetitions * R := hrawCalls
          _ ≤ Q + Q + P := by omega
          _ ≤ 100 * P := by omega
      have hfinalSteps : otherSteps (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤ 100 * P := by
        calc
          _ ≤ otherSteps (CountingMatroid.Program.preprocess
                contract.implementation n r o₁ o₂) +
              otherSteps (CountingMatroid.Program.schedule n p) +
              s.repetitions * (R + 1) +
              (s.repetitions + 1) ^ 2 * (2 * R + 8) := hrawSteps
          _ ≤ Q + Q + 2 * P + 40 * P := by omega
          _ ≤ 100 * P := by omega
      have hpoly : 100 * P =
          (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4)) := by
        calc
          100 * P = 100 * (A * X ^ D) ^ (Dr + 4) := rfl
          _ = 100 * (A ^ (Dr + 4) * (X ^ D) ^ (Dr + 4)) := by
            rw [mul_pow]
          _ = (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4)) := by
            rw [← pow_mul]
            rw [mul_assoc]
      change oracleCalls (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤
          (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4)) ∧
        otherSteps (CountingMatroid.Program.estimate
          contract.implementation n r o₁ o₂ p tape) ≤
          (100 * A ^ (Dr + 4)) * X ^ (D * (Dr + 4))
      rw [← hpoly]
      exact ⟨hfinalCalls, hfinalSteps⟩
    obtain ⟨C, degree, hcost⟩ := hcost
    refine ⟨C, degree, ?_⟩
    intro n r o₁ o₂ p tape hr h
    exact ⟨estimate_none_nonneg contract n r o₁ o₂ p tape h,
      hcost n r o₁ o₂ p tape hr h⟩
  obtain ⟨Cnone, Dnone, hnone⟩ := hnone
  let callCoeff := contract.callConstant * 2 ^ contract.callDegree
  let bitCoeff := contract.bitConstant * 2 ^ contract.bitDegree
  let C := Cnone + callCoeff + bitCoeff + 1
  let degree := Dnone + contract.callDegree + contract.bitDegree + 1
  refine ⟨C, degree, ?_⟩
  intro n r o₁ o₂ p tape hr
  let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹)
  let x := size + 1
  have hx : 1 ≤ x := by dsimp [x]; omega
  have hpower (c d : ℕ) (hc : c ≤ C) (hd : d ≤ degree) :
      c * x ^ d ≤ C * x ^ degree := by
    exact Nat.mul_le_mul hc (pow_le_pow_right₀ hx hd)
  by_cases hp : (CountingMatroid.Program.preprocess contract.implementation
      n r o₁ o₂).val = none
  · obtain ⟨hnonneg, hcalls, hsteps⟩ := hnone n r o₁ o₂ p tape hr hp
    dsimp at hnonneg hcalls hsteps ⊢
    refine ⟨hnonneg, le_trans hcalls ?_, le_trans hsteps ?_⟩
    · exact hpower Cnone Dnone (by dsimp [C]; omega)
        (by dsimp [degree]; omega)
    · exact hpower Cnone Dnone (by dsimp [C]; omega)
        (by dsimp [degree]; omega)
  · cases hq : (CountingMatroid.Program.preprocess contract.implementation
        n r o₁ o₂).val with
    | none => exact False.elim (hp hq)
    | some q =>
        obtain ⟨hnonneg, hcalls, hsteps⟩ :=
          estimate_preliminary_resource_bound contract n r o₁ o₂ p tape q hq
        dsimp at hnonneg hcalls hsteps ⊢
        have hnsize : n ≤ size := by dsimp [size]; omega
        have hbase : n + r + 1 ≤ 2 * x := by
          dsimp [x]
          omega
        have hcallPow := Nat.pow_le_pow_left hbase contract.callDegree
        have hbitPow := Nat.pow_le_pow_left hbase contract.bitDegree
        have hcall : contract.callConstant * (n + r + 1) ^ contract.callDegree ≤
            callCoeff * x ^ contract.callDegree := by
          calc
            _ ≤ contract.callConstant * (2 * x) ^ contract.callDegree :=
              Nat.mul_le_mul_left _ hcallPow
            _ = callCoeff * x ^ contract.callDegree := by
              dsimp [callCoeff]
              rw [mul_pow]
              ring
        have hbit : contract.bitConstant * (n + r + 1) ^ contract.bitDegree ≤
            bitCoeff * x ^ contract.bitDegree := by
          calc
            _ ≤ contract.bitConstant * (2 * x) ^ contract.bitDegree :=
              Nat.mul_le_mul_left _ hbitPow
            _ = bitCoeff * x ^ contract.bitDegree := by
              dsimp [bitCoeff]
              rw [mul_pow]
              ring
        refine ⟨hnonneg, le_trans hcalls (le_trans hcall ?_), ?_⟩
        · exact hpower callCoeff contract.callDegree
            (by dsimp [C]; omega) (by dsimp [degree]; omega)
        · have hbitMain : bitCoeff * x ^ contract.bitDegree ≤
              bitCoeff * x ^ degree :=
            Nat.mul_le_mul_left _ (pow_le_pow_right₀ hx
              (by dsimp [degree]; omega))
          have hone : 1 ≤ x ^ degree := one_le_pow₀ hx
          have hcoef : (bitCoeff + 1) * x ^ degree ≤ C * x ^ degree :=
            Nat.mul_le_mul_right _ (by dsimp [C]; omega)
          change otherSteps (CountingMatroid.Program.estimate
            contract.implementation n r o₁ o₂ p tape) ≤ C * x ^ degree
          calc
            _ ≤ contract.bitConstant * (n + r + 1) ^ contract.bitDegree + 1 :=
              hsteps
            _ ≤ bitCoeff * x ^ contract.bitDegree + 1 :=
              Nat.add_le_add_right hbit 1
            _ ≤ bitCoeff * x ^ degree + x ^ degree :=
              Nat.add_le_add hbitMain hone
            _ = (bitCoeff + 1) * x ^ degree := by ring
            _ ≤ C * x ^ degree := hcoef

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

* r8 · proved · closed the estimator cost and sign bound using the schedule and bounded-run envelopes and a proved median resource module.
* r7 · open · proved exact and bounded early-answer branches; reduced the estimator theorem to the `preprocess = none` branch, whose median scan still needs a rational-length cost invariant.
* r6 · open · split schedule arithmetic and capped-run rational invariants into independently elaborated resource envelopes; the estimator still needs median and charge composition.
* r5 · open · proved charged rational-power value and nonnegativity, and zero oracle calls for rational acceptance; the full polynomial bound still needs rational-size invariants.
* r4 · open · proved zero oracle cost for classification, bounded uniform draws, and paired selection, plus a `2*n` oracle cap for observation recording; rational-size invariants still block the full run bound.
* r3 · open · proved greedy and paired rank oracle caps and zero oracle cost of rational powers; the annealing phase still needs rational-size invariants.
* r2 · open · proved charged bind/loop and pretest resource lemmas; the annealing phase bound still needs rational-size invariants.
* r1 · open · proved support transport and added `r ≤ n`; the per-run charged polynomial bound remains unproved.
-/
