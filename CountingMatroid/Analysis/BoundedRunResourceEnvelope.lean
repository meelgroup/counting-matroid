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
  · -- BLOCKER: The positive-phase case needs an invariant for currentWeights,
    -- stored tables, numeratorSum, product, and the charged phase costs.
    sorry

end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · partial recovery · proved the zero-phase oracle and quadratic work bounds and integrated the entire zero-phase case into the envelope; the positive-phase joint invariant remains open.
* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/
