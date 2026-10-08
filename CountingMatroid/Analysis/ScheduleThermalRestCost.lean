import CountingMatroid.Analysis.ScheduleThermalSetupCost

/-!
# Cost of the schedule tail

The setup phases have separate checked cost bounds. This module isolates the
charged powers, observation count, draw width, and confidence repetition cost.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The remaining charged schedule operations have a polynomial
nonoracle charge after the opening and thermal setup phases.
TEXLINE: main.tex:1348-1358 -/
theorem thermalRest_otherSteps_poly (n r : ℕ) (p : InputParams) :
    let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1
    let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
    let L := 2 * n * (n + b)
    let D := 32 * (L + 1)
    otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
      10 ^ 150 * S ^ 40 := by
  -- BLOCKER: An unphased expansion of thermalRest yields nested values for
  -- 22 charged operations, including three powers and the observation ceiling.
  -- A phase-local cost identity is needed before the available size bounds
  -- can be applied. The source statement is the precise bound consumed by
  -- schedule_otherSteps_envelope.
  sorry

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
