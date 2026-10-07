import CountingMatroid.Model.Run

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The charged schedule construction produces polynomially bounded
loop caps and a nonnegative annealing base. This is independent of the phase
state and of the median computation.
TEXLINE: main.tex:1348-1356, 1397-1421 -/
theorem schedule_resource_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let schedule := CountingMatroid.Program.schedule n p
      let s := schedule.val
      0 ≤ s.ρ ∧
      n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
        binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree ∧
      oracleCalls schedule ≤ C * inputSize ^ degree ∧
      otherSteps schedule ≤ C * inputSize ^ degree := by
  -- BLOCKER: The least-halving and least-draw-trial loops need value and
  -- bit-cost bounds before the schedule fields can be bounded together.
  sorry

end CountingMatroid.Analysis.ScheduleResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r6 · open · isolated schedule arithmetic from the capped-run state invariant.
-/
