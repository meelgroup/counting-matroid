import CountingMatroid.Model.Program
import CountingMatroid.Analysis.RationalHeight
import CountingMatroid.Analysis.EstimateMedianResource
import CountingMatroid.Analysis.ScheduleCostPrimitives

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: The charged rational-power loop computes exponentiation. -/
theorem ratPower_value (base : ℚ) (exponent : ℕ) :
    (CountingMatroid.Program.ratPower base exponent).val = base ^ exponent := by
  have fold_value (l : List ℕ) (acc : ℚ) :
      (Arlib.Computation.Charged.foldl (fun acc _ => ratMul acc base) l acc).val =
        acc * base ^ l.length := by
    induction l generalizing acc with
    | nil => simp
    | cons _ xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons, ih]
        simp [ratMul, pow_succ]
        ring
  unfold CountingMatroid.Program.ratPower Arlib.Computation.Charged.repeatFor
  simpa using fold_value (List.range exponent) 1

/-- INTERNAL: A charged finite loop preserves any invariant preserved by its body. -/
theorem chargedFold_preserves {ι β : Type} (P : β → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i, P b → P (f b i).val) (l : List ι) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f l b).val := by
  induction l generalizing b with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hf b i hb)

/-- INTERNAL: A charged finite loop preserves a counter bound that grows by one
per iteration. -/
theorem chargedFold_count_growth {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b i k, P b k → P (f b i).val (k + 1))
    (l : List ι) (b : β) (k : ℕ) (hb : P b k) :
    P (Arlib.Computation.Charged.foldl f l b).val (k + l.length) := by
  induction l generalizing b k with
  | nil => simpa using hb
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (f b i).val (k + 1) (hf b i k hb)

/-- INTERNAL: Recording one state raises each type count by at most one.
TEXLINE: main.tex:1362-1369 -/
theorem recordObservation_counts_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ)
    (current next : CountingMatroid.Program.ObservationCursor n) (k : ℕ)
    (hcounts : ∀ kind, current.counts kind ≤ k)
    (h : (CountingMatroid.Program.recordObservation r o₁ o₂ rho current).val =
      some next) : ∀ kind, next.counts kind ≤ k + 1 := by
  simp only [CountingMatroid.Program.recordObservation,
    Arlib.Computation.Charged.val_bind] at h
  split at h
  · simp at h
  · simp [countIncrement] at h
    subst next
    intro kind
    change (if kind = (CountingMatroid.Program.classifyState current.state).val then
      current.counts kind + 1 else current.counts kind) ≤ k + 1
    split_ifs <;> have := hcounts kind <;> omega
  · simp only [Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure] at h
    cases Option.some.inj h
    intro kind
    simp only [countIncrement, Arlib.Computation.Charged.val_opMany]
    split_ifs <;> have := hcounts kind <;> omega

/-- INTERNAL: Every type count in a completed observation phase is bounded by
its number of observations. TEXLINE: main.tex:1362-1369 -/
theorem observePhase_counts_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ)
    (next : CountingMatroid.Program.ObservationCursor n)
    (h : (CountingMatroid.Program.observePhase r o₁ o₂ tape s q weights start).val =
      some next) : ∀ kind, next.counts kind ≤ s.observations := by
  let P : Option (CountingMatroid.Program.ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ next, acc = some next → ∀ kind, next.counts kind ≤ k
  let f : Option (CountingMatroid.Program.ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell
        (Option (CountingMatroid.Program.ObservationCursor n)) :=
    fun acc index =>
      match acc with
      | none => pure none
      | some current => do
          let onStart ← natEqual index 0
          if onStart then CountingMatroid.Program.recordObservation r o₁ o₂ s.ρ current
          else do
            let next ← CountingMatroid.Program.chainStep r o₁ o₂ tape s.drawTrials q
              weights current.state current.bitCursor
            match next with
            | none => pure none
            | some (state, bitCursor) =>
                CountingMatroid.Program.recordObservation r o₁ o₂ s.ρ
                  ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hstep : ∀ acc index k, P acc k → P (f acc index).val (k + 1) := by
    intro acc index k hacc next hnext
    cases acc with
    | none => simp [f] at hnext
    | some current =>
        dsimp [f] at hnext
        by_cases hon : (natEqual index 0).val = true
        · simp only [hon, ite_true] at hnext
          exact recordObservation_counts_le r o₁ o₂ s.ρ current next k
            (hacc current rfl) hnext
        · simp only [Bool.not_eq_true] at hon
          simp only [hon, Bool.false_eq_true, ↓reduceIte,
            Arlib.Computation.Charged.val_bind] at hnext
          split at hnext
          · simp at hnext
          · apply recordObservation_counts_le r o₁ o₂ s.ρ _ next k ?_ hnext
            exact hacc current rfl
  unfold CountingMatroid.Program.observePhase at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  unfold Arlib.Computation.Charged.repeatFor at h
  have hinit : P (some ⟨start.1, start.2, (allocateCounts n).val, 0⟩) 0 := by
    intro initial hin kind
    cases Option.some.inj hin
    simp [allocateCounts]
  have hfinal := chargedFold_count_growth P f hstep
    (List.range s.observations) _ 0 hinit
  simpa using hfinal next h

/-- INTERNAL: The phase power has binary length linear in its exponent and
the encoding length of the base. TEXLINE: main.tex:1384-1390 -/
theorem ratPower_binary_length_le (q : ℚ) (j : ℕ) :
    binaryRatLength (CountingMatroid.Program.ratPower q j).val ≤
      binaryRatLength 1 + j * binaryRatLength q := by
  rw [ratPower_value]
  induction j with
  | zero => simp
  | succ j ih =>
      rw [pow_succ]
      have hmul :=
        CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.binaryRatLength_mul_le
          (q ^ j) q
      calc
        binaryRatLength (q ^ j * q) ≤ binaryRatLength (q ^ j) + binaryRatLength q := hmul
        _ ≤ binaryRatLength 1 + j * binaryRatLength q + binaryRatLength q :=
          Nat.add_le_add_right ih _
        _ = binaryRatLength 1 + (j + 1) * binaryRatLength q := by ring

/-- INTERNAL: The charged rational product costs at most the square of the
operand encoding lengths. TEXLINE: main.tex:1384-1390 -/
theorem otherSteps_ratMul_le (a b : ℚ) :
    otherSteps (ratMul a b) ≤ (binaryRatLength a + binaryRatLength b) ^ 2 := by
  simp only [otherSteps, ratMul, Arlib.Computation.Charged.cost_opMany,
    Arlib.Computation.CostVec.many]
  simp [Arlib.Computation.Op.all, binaryRatLength, binaryNatLength]
  change ((a.num.natAbs.log2 + a.den.log2 + 3) +
    (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2 ≤ _
  apply Nat.pow_le_pow_left
  omega

/-- INTERNAL: Every intermediate value in a charged rational-power fold has
bounded encoding length, giving a uniform per-step charge.
TEXLINE: main.tex:1384-1390 -/
theorem ratPower_fold_otherSteps_le (q acc : ℚ) (l : List ℕ) :
    otherSteps (Arlib.Computation.Charged.foldl
      (fun current _ => ratMul current q) l acc) ≤
      l.length * (binaryRatLength acc + l.length * binaryRatLength q) ^ 2 := by
  induction l generalizing acc with
  | nil => simp [otherSteps]
  | cons i rest ih =>
      rw [show Arlib.Computation.Charged.foldl
        (fun current _ => ratMul current q) (i :: rest) acc =
        ratMul acc q >>= fun next => Arlib.Computation.Charged.foldl
          (fun current _ => ratMul current q) rest next from rfl,
        CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
      have hhead := otherSteps_ratMul_le acc q
      have htail := ih (acc * q)
      have hlength :=
        CountingMatroid.Analysis.ScheduleOtherStepsEnvelope.binaryRatLength_mul_le acc q
      simp only [ratMul] at htail
      simp only [List.length_cons]
      have hsmall : binaryRatLength acc + binaryRatLength q ≤
          binaryRatLength acc + (rest.length + 1) * binaryRatLength q := by
        nlinarith
      have hlarge : binaryRatLength (acc * q) +
          rest.length * binaryRatLength q ≤
          binaryRatLength acc + (rest.length + 1) * binaryRatLength q := by
        nlinarith
      have hfirst := (hhead.trans (Nat.pow_le_pow_left hsmall 2))
      have hremaining := Nat.mul_le_mul_left rest.length
        (Nat.pow_le_pow_left hlarge 2)
      calc
        otherSteps (ratMul acc q) +
          otherSteps (Arlib.Computation.Charged.foldl
            (fun current _ => ratMul current q) rest (acc * q)) ≤
          (binaryRatLength acc + binaryRatLength q) ^ 2 +
            rest.length * (binaryRatLength (acc * q) +
              rest.length * binaryRatLength q) ^ 2 := Nat.add_le_add hhead htail
        _ ≤ (binaryRatLength acc + (rest.length + 1) * binaryRatLength q) ^ 2 +
            rest.length * (binaryRatLength acc +
              (rest.length + 1) * binaryRatLength q) ^ 2 :=
          Nat.add_le_add (Nat.pow_le_pow_left hsmall 2) hremaining
        _ = (rest.length + 1) *
            (binaryRatLength acc + (rest.length + 1) * binaryRatLength q) ^ 2 := by
          ring

/-- INTERNAL: The phase-power computation has polynomial nonoracle charge.
TEXLINE: main.tex:1384-1390 -/
theorem ratPower_otherSteps_le (q : ℚ) (j : ℕ) :
    otherSteps (CountingMatroid.Program.ratPower q j) ≤
      j * (binaryRatLength 1 + j * binaryRatLength q) ^ 2 := by
  unfold CountingMatroid.Program.ratPower Arlib.Computation.Charged.repeatFor
  simpa using ratPower_fold_otherSteps_le q 1 (List.range j)

/-- INTERNAL: One observation has additive component-height growth, independently
of the state and of the supplied oracles. TEXLINE: main.tex:1362-1378 -/
theorem recordObservation_height_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ)
    (current next : CountingMatroid.Program.ObservationCursor n)
    (h : (CountingMatroid.Program.recordObservation r o₁ o₂ rho current).val =
      some next) : rationalHeight next.numeratorSum ≤ rationalHeight current.numeratorSum +
        (binaryRatLength 1 + n * binaryRatLength rho + 1) := by
  simp only [CountingMatroid.Program.recordObservation,
    Arlib.Computation.Charged.val_bind] at h
  split at h
  · simp at h
  · simp [countIncrement] at h
    subst next
    exact Nat.le_add_right _ _
  · simp only [Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure] at h
    cases Option.some.inj h
    simp only [ratAdd, Arlib.Computation.Charged.val_opMany,
      CountingMatroid.Model.Operations.natSub, Arlib.Computation.Charged.val_op]
    have hp := ratPower_binary_length_le rho
      (n - (pairedRank r o₁ o₂ current.state).val)
    have hh := rationalHeight_le_length
      (CountingMatroid.Program.ratPower rho
        (n - (pairedRank r o₁ o₂ current.state).val)).val
    have ha := rationalHeight_add_le current.numeratorSum
      (CountingMatroid.Program.ratPower rho
        (n - (pairedRank r o₁ o₂ current.state).val)).val
    have hm := Nat.mul_le_mul_right (binaryRatLength rho)
      (Nat.sub_le n (pairedRank r o₁ o₂ current.state).val)
    omega

/-- INTERNAL: The observation accumulator has linear height growth in the loop cap.
TEXLINE: main.tex:1362-1378 -/
theorem observePhase_height_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ)
    (next : CountingMatroid.Program.ObservationCursor n)
    (h : (CountingMatroid.Program.observePhase r o₁ o₂ tape s q weights start).val =
      some next) : rationalHeight next.numeratorSum ≤
      1 + s.observations * (binaryRatLength 1 + n * binaryRatLength s.ρ + 1) := by
  let K := binaryRatLength 1 + n * binaryRatLength s.ρ + 1
  let P : Option (CountingMatroid.Program.ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ next, acc = some next → rationalHeight next.numeratorSum ≤ 1 + k * K
  let f : Option (CountingMatroid.Program.ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell
        (Option (CountingMatroid.Program.ObservationCursor n)) :=
    fun acc index =>
      match acc with
      | none => pure none
      | some current => do
          let onStart ← natEqual index 0
          if onStart then CountingMatroid.Program.recordObservation r o₁ o₂ s.ρ current
          else do
            let next ← CountingMatroid.Program.chainStep r o₁ o₂ tape s.drawTrials q
              weights current.state current.bitCursor
            match next with
            | none => pure none
            | some (state, bitCursor) =>
                CountingMatroid.Program.recordObservation r o₁ o₂ s.ρ
                  ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hstep : ∀ acc index k, P acc k → P (f acc index).val (k + 1) := by
    intro acc index k hacc next hnext
    cases acc with
    | none => simp [f] at hnext
    | some current =>
        dsimp [f] at hnext
        by_cases hon : (natEqual index 0).val = true
        · simp only [hon, ite_true] at hnext
          have hcur := hacc current rfl
          have hg := recordObservation_height_le r o₁ o₂ s.ρ current next hnext
          dsimp [K] at *
          nlinarith
        · simp only [Bool.not_eq_true] at hon
          simp only [hon, Bool.false_eq_true, ↓reduceIte,
            Arlib.Computation.Charged.val_bind] at hnext
          split at hnext
          · simp at hnext
          · have hcur := hacc current rfl
            have hg := recordObservation_height_le r o₁ o₂ s.ρ _ next hnext
            dsimp [K, P] at *
            nlinarith
  unfold CountingMatroid.Program.observePhase at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  unfold Arlib.Computation.Charged.repeatFor at h
  have hinit : P (some ⟨start.1, start.2, (allocateCounts n).val, 0⟩) 0 := by
    intro initial hin
    cases Option.some.inj hin
    norm_num [rationalHeight, Nat.log2_eq_log_two]
  have hfinal := chargedFold_count_growth P f hstep
    (List.range s.observations) _ 0 hinit
  simpa using hfinal next h

/-- INTERNAL: Successful finishing contributes only the accumulator length and
three bounded natural-count encodings to the ratio. TEXLINE: main.tex:1370-1378 -/
theorem finishPhase_ratio_length_le {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : CountingMatroid.Program.ObservationCursor n)
    (hc : observed.counts .transversal ≤ s.observations)
    (ratio : ℚ) (nextWeights : Multipliers n)
    (h : (CountingMatroid.Program.finishPhase s j weights observed).val =
      some (ratio, nextWeights)) :
    binaryRatLength ratio ≤ binaryRatLength observed.numeratorSum +
      3 * (s.observations + 4) := by
  simp only [CountingMatroid.Program.finishPhase,
    Arlib.Computation.Charged.val_bind] at h
  split at h
  · simp at h
  · simp only [Arlib.Computation.Charged.val_bind, ratOfNat, ratDiv,
      Arlib.Computation.Charged.val_opMany] at h
    split at h
    · simp at h
    · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq,
        Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩
      have hcast (m : ℕ) : binaryRatLength (m : ℚ) ≤ m + 4 := by
        rw [ScheduleOtherStepsEnvelope.binaryRatLength_natCast]
        have hm := Nat.log_le_self 2 m
        rw [← Nat.log2_eq_log_two] at hm
        omega
      have hobs := hcast s.observations
      have hcount := hcast (observed.counts .transversal)
      have hu := ScheduleOtherStepsEnvelope.binaryRatLength_div_le
        observed.numeratorSum (s.observations : ℚ)
      have hp := ScheduleOtherStepsEnvelope.binaryRatLength_div_le
        (observed.counts .transversal : ℚ) (s.observations : ℚ)
      have hr := ScheduleOtherStepsEnvelope.binaryRatLength_div_le
        (observed.numeratorSum / (s.observations : ℚ))
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
      simp only [countRead, Arlib.Computation.Charged.val_opMany]
      omega

end CountingMatroid.Analysis.BoundedRunResourceEnvelope
