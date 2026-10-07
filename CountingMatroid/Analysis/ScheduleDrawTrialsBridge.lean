import CountingMatroid.Model.Program

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleDrawTrialsBridge

open CountingMatroid.Model

/-- INTERNAL: The schedule's trial count is controlled by its charged draw-call count.
TEXLINE: main.tex:1397-1421 -/
theorem schedule_drawTrials_le_drawCalls (n : ℕ) (p : InputParams) :
    let s := (CountingMatroid.Program.schedule n p).val
    s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9 := by
  -- BLOCKER: The defining equality with leastDrawTrials does not elaborate
  -- promptly by `rfl`, nor by unfolding and simplifying the whole schedule;
  -- both routes expand the observation quotient through every schedule field.
  sorry

end CountingMatroid.Analysis.ScheduleDrawTrialsBridge
