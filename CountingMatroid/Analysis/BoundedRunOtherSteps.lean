import CountingMatroid.Model.Program
import CountingMatroid.Analysis.RationalHeight

set_option autoImplicit false

/-!
The outstanding nonoracle-work bound for a capped run. Its proof needs a
reachable-state invariant for current and stored multiplier lengths, together
with observation accumulator/count bounds and the running product length.
Unlike the output bound, this must account for work already spent on paths that
abort during `restartPhase`, `observePhase`, or `finishPhase`.
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
  -- BLOCKER: Unfolding boundedRun and rewriting otherSteps_bind leaves the
  -- repeatFor charge and a final ratMul charge depending on its returned product.
  -- The available otherSteps_foldl_le_of_mem quantifies over arbitrary cursors;
  -- it cannot bound arbitrary stored rational multipliers. Prove an invariant
  -- bounding every current/stored weight after each completed phase, then bound
  -- chainStep (including boundedUniform on the ratio denominator), traceReturn,
  -- restartPhase, observePhase, and finishPhase on every charged path.
  -- The parent now proves output length by observation-height/product induction;
  -- that successful-output invariant alone does not bound charges before abort.
  sorry
end CountingMatroid.Analysis.BoundedRunOtherSteps

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · open handoff · unfolding boundedRun and rewriting otherSteps_bind exposes the phase-loop charge; a reachable multiplier-and-work invariant remains required, including rejected draws and failed finishPhase scans.
-/
