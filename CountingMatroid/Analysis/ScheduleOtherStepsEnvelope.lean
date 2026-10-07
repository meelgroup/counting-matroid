import CountingMatroid.Model.Run

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The nonoracle charges of the concrete schedule have a common
polynomial bound in the encoded input size.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_otherSteps_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      otherSteps (CountingMatroid.Program.schedule n p) ≤
        C * inputSize ^ degree := by
  -- BLOCKER: Directly expanding the charged schedule leaves a sum of costs
  -- for rational operands whose encoding sizes must be bounded. In particular
  -- the halving-loop rationals, η² and the observation quotient need bounds.
  sorry

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
