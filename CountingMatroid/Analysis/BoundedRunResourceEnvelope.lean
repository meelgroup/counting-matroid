import CountingMatroid.Model.Program

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
  · -- BLOCKER: The three remaining quantitative bounds require one phase invariant
    -- for every current/stored multiplier, the observation numeratorSum, and the
    -- running product. Their lengths determine the rational-operation charges
    -- and the widths of the capped uniform draws inside nested phase loops.
    refine ⟨boundedRun_value_nonneg n r o₁ o₂ tape s hρ, ?_⟩
    sorry

end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r9 · partial recovery · proved nonnegativity of every successful observation accumulator, completed phase ratio, and bounded-run output; the three positive-phase quantitative bounds still need a joint phase-state invariant.
* r8 · partial recovery · proved the zero-phase oracle and quadratic work bounds and integrated the entire zero-phase case into the envelope; the positive-phase joint invariant remains open.
* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/
