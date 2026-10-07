import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapeProductAccuracy

open CountingMatroid.Model

/-- INTERNAL: At most one eighth of capped finite tapes yield a completed
product farther than ε/4 from the concrete final transversal partition sum.
This is the conditional restart and observation analysis, learned-weight
induction, product estimate, and uncapped-to-capped tape coupling.
TEXLINE: main.tex:1207-1315,1392-1421 -/
theorem finite_tape_product_accuracy (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let c := CountingMatroid.Analysis.TransversalPartition.partitionSum
      r o₁ o₂ (s.ρ ^ s.L)
    (Set.ncard {bits : List Bool | bits.length = m ∧
      let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
      y ≠ 0 ∧
        (y < (1 - p.ε / 4) * c ∨
         (1 + p.ε / 4) * c < y)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  -- BLOCKER: No law for an uncapped run, conditional stationary phase bound,
  -- or coupling to `singleRun` has been formalized. `Program.boundedRun`
  -- retains only estimate and bit cursor after folding phase status.
  sorry

end CountingMatroid.Analysis.FiniteTapeProductAccuracy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · open · `aesop` leaves the finite-tape product-event bound; no conditional phase law or uncapped-to-capped coupling is formalized.
-/
