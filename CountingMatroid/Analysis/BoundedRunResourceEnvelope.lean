import CountingMatroid.Model.Program

set_option autoImplicit false

namespace CountingMatroid.Analysis.BoundedRunResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

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
  -- BLOCKER: The phase induction needs an invariant bounding the bit lengths
  -- of every stored multiplier and the running product after each update.
  -- The observation induction also needs a bound on the numerator accumulator.
  sorry

end CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r6 · open · isolated the capped-run phase invariant from schedule construction and amplification.
-/
