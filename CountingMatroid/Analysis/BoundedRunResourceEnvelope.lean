import CountingMatroid.Model.Program
import CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
import CountingMatroid.Analysis.BoundedRunOracleCalls

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged natural-power fold computes exponentiation. -/
private theorem natPower_fold_value (base : ℕ) (l : List ℕ) (acc : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).val =
      acc * base ^ l.length := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih]
      simp [natMul, pow_succ]
      ring

/-- INTERNAL: The charged natural power loop computes exponentiation. -/
theorem natPower_value (base exponent : ℕ) :
    (CountingMatroid.Program.natPower base exponent).val = base ^ exponent := by
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using natPower_fold_value base (List.range exponent) 1

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

/-- INTERNAL: Recording an observation preserves a nonnegative rational accumulator.
TEXLINE: main.tex:1362-1378 -/
theorem recordObservation_numerator_nonneg {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ)
    (current next : CountingMatroid.Program.ObservationCursor n)
    (hρ : 0 ≤ rho) (hcur : 0 ≤ current.numeratorSum)
    (h : (CountingMatroid.Program.recordObservation r o₁ o₂ rho current).val =
      some next) : 0 ≤ next.numeratorSum := by
  simp only [CountingMatroid.Program.recordObservation,
    Arlib.Computation.Charged.val_bind] at h
  split at h
  · simp at h
  · simp [countIncrement] at h
    subst next
    exact hcur
  · simp only [Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure] at h
    cases Option.some.inj h
    simp only [ratAdd, Arlib.Computation.Charged.val_opMany, ratPower_value,
      CountingMatroid.Model.Operations.natSub] at *
    positivity

/-- INTERNAL: A charged finite loop preserves any invariant preserved by its body. -/
private theorem chargedFold_preserves {ι β : Type} (P : β → Prop)
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
private theorem chargedFold_count_growth {ι β : Type} (P : β → ℕ → Prop)
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

/-- INTERNAL: Every successful observation loop has a nonnegative accumulator.
TEXLINE: main.tex:1362-1378 -/
theorem observePhase_numerator_nonneg {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (hρ : 0 ≤ s.ρ)
    (next : CountingMatroid.Program.ObservationCursor n)
    (h : (CountingMatroid.Program.observePhase r o₁ o₂ tape s q weights start).val =
      some next) : 0 ≤ next.numeratorSum := by
  let P : Option (CountingMatroid.Program.ObservationCursor n) → Prop :=
    fun acc => ∀ next, acc = some next → 0 ≤ next.numeratorSum
  let f : ℕ → Option (CountingMatroid.Program.ObservationCursor n) →
      Arlib.Computation.Charged Op Cell
        (Option (CountingMatroid.Program.ObservationCursor n)) :=
    fun index acc =>
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
  have hstep : ∀ acc index, P acc → P (f index acc).val := by
    intro acc index hacc next hnext
    cases acc with
    | none => simp [f] at hnext
    | some current =>
        dsimp [f] at hnext
        by_cases hon : (natEqual index 0).val = true
        · simp only [hon, ite_true] at hnext
          exact recordObservation_numerator_nonneg r o₁ o₂ s.ρ current next hρ
            (hacc current rfl) hnext
        · simp only [Bool.not_eq_true] at hon
          simp only [hon, Bool.false_eq_true, ↓reduceIte,
            Arlib.Computation.Charged.val_bind] at hnext
          split at hnext
          · simp at hnext
          · apply recordObservation_numerator_nonneg r o₁ o₂ s.ρ _ next hρ ?_ hnext
            simpa using hacc current rfl
  unfold CountingMatroid.Program.observePhase at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  unfold Arlib.Computation.Charged.repeatFor at h
  have hinit : P (some ⟨start.1, start.2, (allocateCounts n).val, 0⟩) := by
    intro initial hin
    cases Option.some.inj hin
    exact le_refl _
  exact (chargedFold_preserves P (fun acc index => f index acc) hstep
    (List.range s.observations) _ hinit) next h

/-- INTERNAL: A completed phase has a nonnegative ratio when its accumulator is
nonnegative. TEXLINE: main.tex:1362-1386 -/
theorem finishPhase_ratio_nonneg {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : CountingMatroid.Program.ObservationCursor n)
    (hout : 0 ≤ observed.numeratorSum) (ratio : ℚ) (nextWeights : Multipliers n)
    (h : (CountingMatroid.Program.finishPhase s j weights observed).val =
      some (ratio, nextWeights)) : 0 ≤ ratio := by
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
      exact div_nonneg (div_nonneg hout (by positivity))
        (div_nonneg (by positivity) (by positivity))

/-- INTERNAL: A successful bounded run has a nonnegative product of its phase ratios.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_value_nonneg (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ) :
    0 ≤ (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 := by
  let P : Option (CountingMatroid.Program.AnnealingCursor n) → Prop :=
    fun acc => ∀ current, acc = some current → 0 ≤ current.product
  let f : ℕ → Option (CountingMatroid.Program.AnnealingCursor n) →
      Arlib.Computation.Charged Op Cell
        (Option (CountingMatroid.Program.AnnealingCursor n)) :=
    fun j acc =>
      match acc with
      | none => pure none
      | some current => do
          let q ← CountingMatroid.Program.ratPower s.ρ j
          let started ← CountingMatroid.Program.restartPhase r o₁ o₂ tape s
            current.tables j current.bitCursor
          match started with
          | none => pure none
          | some started =>
              let observed ← CountingMatroid.Program.observePhase r o₁ o₂ tape s q
                current.currentWeights started
              match observed with
              | none => pure none
              | some observed =>
                  let finished ← CountingMatroid.Program.finishPhase s j
                    current.currentWeights observed
                  match finished with
                  | none => pure none
                  | some (ratio, nextWeights) =>
                      let product ← ratMul current.product ratio
                      let next ← successor j
                      let update ← lessThan next s.L
                      if update then
                        let tables ← learnedWeightWrite current.tables next s.L nextWeights
                        pure (some ⟨tables, nextWeights, product, observed.bitCursor⟩)
                      else pure (some ⟨current.tables, nextWeights, product,
                        observed.bitCursor⟩)
  have hstep : ∀ acc j, P acc → P (f j acc).val := by
    intro acc j hacc next hnext
    cases acc with
    | none => simp [f] at hnext
    | some current =>
        dsimp [f] at hnext
        cases hstarted : (CountingMatroid.Program.restartPhase r o₁ o₂ tape s
          current.tables j current.bitCursor).val with
        | none => simp [hstarted] at hnext
        | some started =>
            simp only [hstarted, Arlib.Computation.Charged.val_bind] at hnext
            cases hobserved : (CountingMatroid.Program.observePhase r o₁ o₂ tape s
              (CountingMatroid.Program.ratPower s.ρ j).val current.currentWeights
              started).val with
            | none => simp [hobserved] at hnext
            | some observed =>
                simp only [hobserved, Arlib.Computation.Charged.val_bind] at hnext
                cases hfinished : (CountingMatroid.Program.finishPhase s j
                  current.currentWeights observed).val with
                | none => simp [hfinished] at hnext
                | some result =>
                    rcases result with ⟨ratio, nextWeights⟩
                    simp only [hfinished, Arlib.Computation.Charged.val_bind,
                      ratMul, Arlib.Computation.Charged.val_opMany] at hnext
                    have hratio := finishPhase_ratio_nonneg s j current.currentWeights
                      observed
                      (observePhase_numerator_nonneg r o₁ o₂ tape s
                        (CountingMatroid.Program.ratPower s.ρ j).val
                        current.currentWeights started hρ observed hobserved)
                      ratio nextWeights hfinished
                    split at hnext
                    · simp only [Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure,
                        learnedWeightWrite, Arlib.Computation.Charged.val_opMany] at hnext
                      cases Option.some.inj hnext
                      exact mul_nonneg (hacc current rfl) hratio
                    · simp only [Arlib.Computation.Charged.val_pure] at hnext
                      cases Option.some.inj hnext
                      exact mul_nonneg (hacc current rfl) hratio
  unfold CountingMatroid.Program.boundedRun
  simp only [Arlib.Computation.Charged.val_bind]
  unfold Arlib.Computation.Charged.repeatFor
  have hinit : P (some ⟨(allocateLearnedWeights n s.L (initialWeights n).val).val,
      (initialWeights n).val, 1, 0⟩) := by
    intro current hc
    cases Option.some.inj hc
    exact zero_le_one
  have hphases := chargedFold_preserves P (fun acc j => f j acc) hstep
    (List.range s.L) _ hinit
  split
  · simp
  · simp only [Arlib.Computation.Charged.val_bind, natPower_value,
      ratOfNat, ratMul, Arlib.Computation.Charged.val_opMany]
    exact mul_nonneg (by positivity) (hphases _ (by assumption))

/-- INTERNAL: With no annealing phases the run returns the initial scale.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_zero_phases_value (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hL : s.L = 0) :
    (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 = (2 ^ n : ℚ) := by
  simp [CountingMatroid.Program.boundedRun, hL, natPower_value,
    ratMul, ratOfNat,
    Arlib.Computation.Charged.repeatFor]

/-- INTERNAL: An integer-power loop spends no independence-oracle calls. -/
private theorem natPower_oracle_cost_zero (base : ℕ) (l : List ℕ) (acc : ℕ)
    (op : Op) (hop : op ≠ Op.word .mul) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).cost op = 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.cost_foldl_cons]
      change (natMul acc base).cost op +
        (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) xs
          (natMul acc base).val).cost op = 0
      rw [ih]
      simp [natMul, Arlib.Computation.CostVec.one, hop]

/-- INTERNAL: The zero-phase run makes no independence-oracle calls.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_zero_phases_oracleCalls (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hL : s.L = 0) :
    oracleCalls (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) = 0 := by
  simp [CountingMatroid.Program.boundedRun, hL,
    CountingMatroid.Program.natPower, Arlib.Computation.Charged.repeatFor,
    oracleCalls, initialWeights, allocateLearnedWeights, ratOfNat, ratMul, natMul,
    Arlib.Computation.CostVec.many]
  constructor
  · exact natPower_oracle_cost_zero 2 (List.range n) 1 Op.oracleFirst (by decide)
  · exact natPower_oracle_cost_zero 2 (List.range n) 1 Op.oracleSecond (by decide)

/-- INTERNAL: Every iteration of the integer-power loop charges exactly one multiplication. -/
private theorem natPower_cost (base : ℕ) (l : List ℕ) (acc : ℕ) (op : Op) :
    (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).cost op =
      if op = Op.word .mul then l.length else 0 := by
  induction l generalizing acc with
  | nil => simp
  | cons _ xs ih =>
      rw [Arlib.Computation.Charged.cost_foldl_cons]
      change (natMul acc base).cost op +
        (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) xs
          (natMul acc base).val).cost op = _
      rw [ih]
      simp only [natMul, Arlib.Computation.Charged.cost_op,
        Arlib.Computation.CostVec.one, List.length_cons]
      split_ifs <;> omega

set_option maxHeartbeats 1000000 in
/-- INTERNAL: The zero-phase run has quadratic charged work.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_zero_phases_otherSteps (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hL : s.L = 0) :
    otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤
      100 * (n + 1) ^ 2 := by
  simp [CountingMatroid.Program.boundedRun, hL,
    CountingMatroid.Program.natPower, Arlib.Computation.Charged.repeatFor,
    otherSteps, initialWeights, allocateLearnedWeights, ratOfNat, ratMul,
    Arlib.Computation.CostVec.many, natPower_cost, natPower_fold_value,
    Arlib.Computation.Op.all]
  change n + (((2 ^ n : ℚ).num.natAbs.log2 + (2 ^ n : ℚ).den.log2 + 3 +
      ((1 : ℚ).num.natAbs.log2 + (1 : ℚ).den.log2 + 3))) ^ 2 +
      (n + 1) + (n * n + 1) ≤ 100 * (n + 1) ^ 2
  simp [Nat.log2_two_pow]
  have hlog : Nat.log2 1 = 0 := by decide
  simp [hlog] at *
  nlinarith [sq_nonneg (n : ℤ)]

/-- INTERNAL: The exact initial scale has linear binary length. -/
private theorem binaryRatLength_two_pow (n : ℕ) :
    binaryRatLength (2 ^ n : ℚ) = n + 4 := by
  simp [binaryRatLength, binaryNatLength, Nat.log2_two_pow]
  have h : Nat.log2 1 = 0 := by decide
  simp [h]
  omega

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
private theorem ratPower_fold_otherSteps_le (q acc : ℚ) (l : List ℕ) :
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

/-- INTERNAL: The capped run has a resource bound expressed only in the
schedule fields that its code reads. This separates the phase-state invariant
from the arithmetic used to construct the schedule and amplify the answer.
TEXLINE: main.tex:1350-1440 -/
theorem boundedRun_resource_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
      (tape : ℕ → Bool) (s : AnnealingSchedule),
      0 ≤ s.ρ →
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      let run := CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0
      0 ≤ run.val.1 ∧
      binaryRatLength run.val.1 ≤ C * size ^ degree ∧
      oracleCalls run ≤ C * size ^ degree ∧
      otherSteps run ≤ C * size ^ degree := by
  refine ⟨100, 100, ?_⟩
  intro n r o₁ o₂ tape s hρ
  dsimp only
  by_cases hL : s.L = 0
  · let size := n + s.L + s.τ + s.restartCap + s.observations +
      s.drawTrials + binaryRatLength s.ρ + 1
    have hsize : n + 1 ≤ size := by dsimp [size]; omega
    have hquad : 100 * (n + 1) ^ 2 ≤ 100 * size ^ 100 := by
      have hpow : (n + 1) ^ 2 ≤ size ^ 2 := Nat.pow_le_pow_left hsize 2
      have hstep : size ^ 2 ≤ size ^ 100 := Nat.pow_le_pow_right (by omega) (by omega)
      exact Nat.mul_le_mul_left 100 (hpow.trans hstep)
    rw [boundedRun_zero_phases_value n r o₁ o₂ tape s hL]
    constructor
    · positivity
    constructor
    · rw [binaryRatLength_two_pow]
      calc
        n + 4 ≤ 100 * (n + 1) ^ 2 := by nlinarith only
        _ ≤ 100 * size ^ 100 := hquad
    constructor
    · rw [boundedRun_zero_phases_oracleCalls n r o₁ o₂ tape s hL]
      exact Nat.zero_le _
    · exact (boundedRun_zero_phases_otherSteps n r o₁ o₂ tape s hL).trans hquad
  · -- BLOCKER: The output-size and nonoracle-charge bounds require a phase invariant
    -- for every reachable current/stored multiplier, observation numeratorSum,
    -- observation type count (at most s.observations), and running product.
    -- A bound on all AnnealingCursor values cannot serve as the step hypothesis
    -- of Charged.steps_repeatFor_le: an arbitrary cursor can contain multipliers
    -- of unbounded binary length. Even the isolated charge
    -- otherSteps (ratMul (2 ^ K : ℚ) 1) is at least K for every K.
    -- The invariant must then bound restartPhase, observePhase, and finishPhase
    -- nonoracle costs, including acceptance denominators in capped uniform draws.
    have hphasePower (j : ℕ) :
        binaryRatLength (CountingMatroid.Program.ratPower s.ρ j).val ≤
          binaryRatLength 1 + j * binaryRatLength s.ρ :=
      ratPower_binary_length_le s.ρ j
    have hphasePowerCost (j : ℕ) :
        otherSteps (CountingMatroid.Program.ratPower s.ρ j) ≤
          j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 :=
      ratPower_otherSteps_le s.ρ j
    have hproductCost (a b : ℚ) :
        otherSteps (ratMul a b) ≤ (binaryRatLength a + binaryRatLength b) ^ 2 :=
      otherSteps_ratMul_le a b
    refine ⟨boundedRun_value_nonneg n r o₁ o₂ tape s hρ, ?_, ?_, ?_⟩
    · sorry
    · exact BoundedRunOracleCalls.boundedRun_oracleCalls_envelope
        n r o₁ o₂ tape s
    · sorry

end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r15 · decomposed · separated the state-independent oracle charge into BoundedRunOracleCalls; output size and nonoracle charge still need a reachable-state invariant.
* r14 · partial recovery · proved observation type-count and phase-power charge bounds; the positive-phase rational-size and abort-path invariant remains open.
* r13 · partial recovery · proved phase-power binary length and a quadratic charge bound for rational multiplication; the reachable phase-state and abort-path cost invariant is still missing.
* r12 · open · verified that rational multiplication has unbounded charge on arbitrary input (`otherSteps (ratMul (2 ^ K : ℚ) 1) ≥ K`); a reachable-state invariant must also bound observation counts by the loop length.
* r11 · open · direct simplification exposed the entire positive-phase fold; the generic charged loop bound requires a price for arbitrary cursors, while rational-operation costs are unbounded without a reachable-state length invariant.
* r10 · open · audited arbitrary schedule fields and expanded the positive-phase goal; Arlib's fold cost bound needs a state-length invariant for the stored multiplier tables and phase accumulators, which is still absent.
* r9 · partial recovery · proved nonnegativity of every successful observation accumulator, completed phase ratio, and bounded-run output; the three positive-phase quantitative bounds still need a joint phase-state invariant.
* r8 · partial recovery · proved the zero-phase oracle and quadratic work bounds and integrated the entire zero-phase case into the envelope; the positive-phase joint invariant remains open.
* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/
