import CountingMatroid.Interface.Pseudocode
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.InaccurateNonzeroTapeBound

open CountingMatroid.Model

/-- INTERNAL: At most one eighth of finite tapes complete with a nonzero
estimate outside the relative-error interval. This is the phase-estimation,
multiplier-induction, and product-accuracy part of the run analysis.
TEXLINE: main.tex:1253-1370 -/
theorem inaccurate_nonzero_tape_mass_bound (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
      y ≠ 0 ∧
        (y < (1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ) ∨
         (1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ) < y)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  -- The conditional phase estimates and product induction have not been
  -- formalized for `Program.boundedRun`.
  sorry

end CountingMatroid.Analysis.InaccurateNonzeroTapeBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · open · direct simplification reduces the claim to a nonzero bad-tape count bound; phase estimates and product induction for `Program.boundedRun` are missing.
-/
