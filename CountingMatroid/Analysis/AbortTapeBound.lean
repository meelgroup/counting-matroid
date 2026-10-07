import CountingMatroid.Interface.Pseudocode
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.AbortTapeBound

open CountingMatroid.Model

/-- INTERNAL: At most one eighth of the fair finite tapes make the capped
annealing run return its abort value. This isolates restart, zero-count, and
bounded-draw aborts from inaccurate completed estimates.
TEXLINE: main.tex:1253-1329,1392-1421 -/
theorem abort_tape_mass_bound (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s = 0} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  -- The restart and capped-draw estimates have not been formalized for
  -- `Program.boundedRun`; unfolding the program leaves those estimates open.
  sorry

end CountingMatroid.Analysis.AbortTapeBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · open · direct simplification reduces the claim to an abort-tape count bound; restart and capped-draw estimates for `Program.boundedRun` are missing.
-/
