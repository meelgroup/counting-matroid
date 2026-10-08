import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapeLowerTail

open CountingMatroid.Model

/-- INTERNAL: A one-sided finite-tape form of the paper's successful-phase
product lower bound. Unlike the completed-product error event, this event
includes aborted runs, so it can directly control the zero-output mass.
TEXLINE: main.tex:1253-1315,1392-1421 -/
theorem finite_tape_lower_tail_bound (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let c := CountingMatroid.Analysis.TransversalPartition.partitionSum
      r o₁ o₂ (s.ρ ^ s.L)
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s < (1 - p.ε / 4) * c} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  -- BLOCKER (missing local estimate): `finite_tape_product_accuracy` bounds
  -- only the event `y ≠ 0 ∧ (y < lower ∨ upper < y)`. Applying it here fails
  -- with a type mismatch; even event monotonicity cannot include zero outputs.
  -- `AbortTapeBound.abort_tape_mass_bound` imports and uses this theorem, so
  -- importing it back would be circular. Separate 1/8 bounds on aborts and
  -- completed-product errors would in any case give only 1/4 by a union bound.
  --
  -- The paper DOES supply the mathematical route: main.tex:1207-1285 proves
  -- conditional phase control and total analytic failure at most 1/16;
  -- main.tex:1287-1315 bounds the product on its complement; and
  -- main.tex:1392-1427 adds at most 1/32 for bounded-draw coupling failure.
  -- Thus a joint bad-event cover gives 3/32 ≤ 1/8, including all aborts.
  -- The missing program-specific facts are the conditional restart and
  -- observation laws for each successful history, and their coupling to
  -- `Program.boundedRun`, with every bit read covered by `Run.blockLength`.
  -- `Interface.Pseudocode.chainStepLaw` merely defines a finite-tape PMF;
  -- it supplies neither the uncapped Metropolis identity nor those bounds.
  -- Arlib's `FinProb.markov`, `FinProb.chebyshev`, and
  -- `Arlib.MarkovChains.metropolis_stationary` cannot supply these premises.
  -- A fresh `exact?` probe also fails. No new unproved helper is introduced:
  -- these are same-paper proof obligations, not a cited Prior assumption.
  sorry

end CountingMatroid.Analysis.FiniteTapeLowerTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r15 · blocked · `exact?` found no proof and applying `finite_tape_product_accuracy` failed on its nonzero-output guard; checked the paper's joint 3/32 failure route, whose conditional phase law and bounded finite-tape coupling are absent from the project.
* r14 · open · isolated the positive-ground lower-tail event including aborts; `aesop` and `exact?` cannot supply the conditional phase law or finite-tape coupling.
-/
