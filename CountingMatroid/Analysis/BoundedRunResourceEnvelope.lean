import CountingMatroid.Model.Program

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged natural power loop computes exponentiation. -/
theorem natPower_value (base exponent : ℕ) :
    (CountingMatroid.Program.natPower base exponent).val = base ^ exponent := by
  have hfold : ∀ (l : List ℕ) (acc : ℕ),
      (Arlib.Computation.Charged.foldl (fun acc _ => natMul acc base) l acc).val =
        acc * base ^ l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons _ l ih =>
        intro acc
        simp only [Arlib.Computation.Charged.val_foldl_cons, List.length_cons]
        rw [ih]
        simp [natMul, pow_succ]
        ring
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using hfold (List.range exponent) 1

/-- INTERNAL: With no annealing phases the run returns the initial scale.
TEXLINE: main.tex:1430-1440 -/
theorem boundedRun_zero_phases_value (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hL : s.L = 0) :
    (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 = (2 ^ n : ℚ) := by
  simp [CountingMatroid.Program.boundedRun, hL, natPower_value,
    ratMul, ratOfNat,
    Arlib.Computation.Charged.repeatFor]

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
  -- BLOCKER: The positive-phase case needs a simultaneous invariant for
  -- currentWeights, all earlier entries in tables, product, and bitCursor.
  -- In each phase, the observation loop must bound counts by observations and
  -- numeratorSum's rational length before finishPhase can bound the next
  -- multipliers and ratio. The zero-phase value is isolated above; the same
  -- split still needs explicit cost bounds for the initialization and final
  -- natPower/ratMul operations.
  sorry

end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r7 · partial recovery · proved the charged natural-power value and isolated the zero-phase output; the positive-phase state-and-cost invariant remains open.
* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/
