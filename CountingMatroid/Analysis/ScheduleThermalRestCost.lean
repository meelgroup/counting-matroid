import CountingMatroid.Analysis.ScheduleThermalSetupCost
import CountingMatroid.Analysis.ScheduleCostPrimitives

/-!
# Cost of the schedule tail

The setup phases have separate checked cost bounds. This module proves an exact
cost identity for the charged powers, observation count, draw width, and confidence
repetition computation. The polynomial bound remains open: its existing supporting
length and capped-search lemmas must be extracted from the downstream envelope
module before they can be imported here without a cycle.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Expand the schedule tail into its four power computations,
unit word charges, rational operations, and two capped searches.
TEXLINE: main.tex:1348-1358 -/
theorem thermalRest_cost_eq (n : ℕ) (p : InputParams) (t : ThermalResult) :
    let A := 10000000000 * t.LPlusOne * (CountingMatroid.Program.natPower n 14).val
    let R := 2000 * (CountingMatroid.Program.natPower t.LPlusOne 2).val *
      (CountingMatroid.Program.natPower n 2).val *
      (20 * (CountingMatroid.Program.natPower n 4).val * (n * t.LPlusOne + 2))
    let Q := (A : ℚ) / (t.eta * t.eta)
    otherSteps (thermalRest n p t) =
      otherSteps (CountingMatroid.Program.natPower n 4) +
      otherSteps (CountingMatroid.Program.natPower t.LPlusOne 2) +
      otherSteps (CountingMatroid.Program.natPower n 2) +
      otherSteps (CountingMatroid.Program.natPower n 14) + 14 + (A.log2 + 1) +
      otherSteps (CountingMatroid.Model.Operations.ratMul t.eta t.eta) +
      otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (t.eta * t.eta)) +
      otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) +
      otherSteps (CountingMatroid.Program.leastDrawTrials
        (3 * t.L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) +
      otherSteps (CountingMatroid.Program.leastHalvings p.δ) := by
  have hop {α : Type} (i : Arlib.Computation.Op) (x : α) :
      otherSteps (Arlib.Computation.Charged.op
        (CountingMatroid.Model.Operations.Op.word i) x) = 1 := by
    cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.one]
  have hcast (a : ℕ) :
      otherSteps (CountingMatroid.Model.Operations.ratOfNat a) = a.log2 + 1 := by
    simp [CountingMatroid.Model.Operations.ratOfNat, otherSteps,
      Arlib.Computation.Op.all, Arlib.Computation.CostVec.many]
  have hpure (x : AnnealingSchedule) :
      otherSteps (pure x : Arlib.Computation.Charged
        CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
        AnnealingSchedule) = 0 := by simp [otherSteps]
  dsimp only
  unfold thermalRest
  simp only [CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
  simp only [CountingMatroid.Model.Operations.natAdd,
    CountingMatroid.Model.Operations.natMul, CountingMatroid.Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hop, hcast, hpure]
  simp only [CountingMatroid.Model.Operations.ratOfNat,
    CountingMatroid.Model.Operations.ratMul, CountingMatroid.Model.Operations.ratDiv,
    Arlib.Computation.Charged.val_opMany]
  omega

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
  dsimp only
  rw [thermalRest_cost_eq]
  -- BLOCKER (import layout): The remaining sum needs leastHalvings_value_le,
  -- binaryRatLength_div_le, observationQuotient_length_le, rationalCeil_log2_le,
  -- log2_mul_le, log2_add_le, natPower_otherSteps_eq, and
  -- leastDrawTrials_otherSteps_le. These are already proved in this namespace
  -- in ScheduleOtherStepsEnvelope.lean, which imports this file and uses this
  -- theorem. Extract that file's helper prefix (before openingPolynomial_arith)
  -- into a shared analysis module and import it from both files. The task's
  -- ownership rules prohibit editing the downstream file or duplicating its
  -- existing proofs. Rechecked against the current imports: a Lean stdin probe
  -- reports unknown identifiers for all five public length/search helpers above;
  -- source search finds their definitions only in the downstream module. Move
  -- its helper block before openingPolynomial_arith into ScheduleCostPrimitives,
  -- retaining the namespace and exporting natPower_otherSteps_eq and
  -- rationalBinary_otherSteps_le (currently private). Both modules can then
  -- import that shared module. schedule_otherSteps_envelope itself is circular here and
  -- its existential constants do not imply this explicit bound.
  sorry

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · blocked · confirmed the downstream helper placement with an import-only
  Lean probe and source search; requested a shared ScheduleCostPrimitives module
  with public power and rational-operation cost bounds. No proof debt moved.
* r15 · partial · proved thermalRest_cost_eq and applied it in the target;
  the existing rational-length and capped-search helpers are downstream of
  the target, requiring extraction to a shared module before reuse.
-/
