import CountingMatroid.Model.Program
import CountingMatroid.Analysis.RationalHeight

set_option autoImplicit false

/-!
The outstanding nonoracle-work bound for a capped run. Its proof needs a
reachable-state invariant for current and stored multiplier lengths, together
with observation accumulator/count bounds and the running product length.
Unlike the output bound, this must account for work already spent on paths that
abort during `restartPhase`, `observePhase`, or `finishPhase`.

The bind decomposition below is checked. Existing phase-power and observation
bounds are in the downstream `BoundedRunResourceEnvelope` module, which imports
this module. They must be moved to an upstream analysis module before they can
be reused here; the dependency move alone does not prove the missing multiplier
and abort-path work invariant.
-/

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Isolate the nonoracle-work conjunct of the run resource envelope.
The size includes every schedule field used to determine loop caps or rational
operands, and the bound includes all abort paths.
TEXLINE: main.tex:1348-1440 -/
theorem boundedRun_otherSteps_envelope :
    ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
      (s : AnnealingSchedule), 0 ≤ s.ρ →
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤
        100 * size ^ 100 := by
  intro n r o₁ o₂ tape s hρ
  dsimp only
  unfold CountingMatroid.Program.boundedRun
  rw [CountingMatroid.Analysis.ResourceBound.otherSteps_bind,
    CountingMatroid.Analysis.ResourceBound.otherSteps_bind,
    CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
  -- BLOCKER (dependency placement): the remaining goal is the sum of the
  -- initialWeights, allocateLearnedWeights, repeatFor, and finalization charges.
  -- These proved prerequisites are in the downstream module
  -- CountingMatroid.Analysis.BoundedRunResourceEnvelope, which imports this file:
  --   ratPower_binary_length_le, otherSteps_ratMul_le, ratPower_otherSteps_le,
  --   observePhase_counts_le, observePhase_height_le, finishPhase_ratio_length_le.
  -- The last two are private as well. Move that module's supporting declarations
  -- (everything before boundedRun_resource_envelope) into an upstream analysis
  -- module, preserving public names and exposing the helpers needed by both
  -- consumers. Import it here and in BoundedRunResourceEnvelope; do not import
  -- BoundedRunResourceEnvelope here or duplicate its existing proofs.
  -- BLOCKER (remaining local lemma): after that move, bound each phase charge
  -- under an invariant on currentWeights, tables, and product, and prove that
  -- successful phases preserve the invariant. In particular finishPhase must
  -- bound intermediate updated multipliers even if a later zero count aborts.
  -- The generic otherSteps_foldl_le_of_mem asks for a bound on arbitrary cursors,
  -- so it does not discharge this reachable-state obligation. The observation
  -- count/height bounds above are needed both for finishPhase charges and for
  -- its returned product factor; output nonnegativity alone cannot replace them.
  sorry
end CountingMatroid.Analysis.BoundedRunOtherSteps

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · blocked · checked the three-bind charge decomposition; identified existing power/count/height prerequisites behind the downstream import and requested their mechanical extraction, without adding helper proof debt.
* r16 · open handoff · unfolding boundedRun and rewriting otherSteps_bind exposes the phase-loop charge; a reachable multiplier-and-work invariant remains required, including rejected draws and failed finishPhase scans.
-/
