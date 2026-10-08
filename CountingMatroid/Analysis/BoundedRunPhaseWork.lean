import CountingMatroid.Analysis.BoundedRunPhase
import CountingMatroid.Analysis.RationalHeight

set_option autoImplicit false
namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

/-- INTERNAL: Bound the full work of one phase from its input rational-size
invariant, including work spent before a rejected draw or zero-count abort.
The input invariant is essential: arbitrary cursor rationals have unbounded
encoding lengths. No conclusion of phase_preserves_size is assumed here.
TEXLINE: main.tex:1348-1440 -/
theorem phase_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    otherSteps (boundedRunPhase r o₁ o₂ tape s j acc) ≤ (runSize n s) ^ 40 := by
  cases acc with
  | none => simp [boundedRunPhase, otherSteps]
  | some current =>
      unfold boundedRunPhase
      rw [CountingMatroid.Analysis.ResourceBound.otherSteps_bind,
        CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
      -- BLOCKER: the goal is phase-power charge plus restart charge plus the
      -- observation/finish continuation. ratPower_otherSteps_le is proved
      -- downstream in BoundedRunResourceEnvelope and needs extraction.
      -- New subroutine cost bounds must track bounded weight lengths through
      -- restart/chainStep and observation/finish scans, including abort paths.
      -- An unrestricted fold bound loses the rational-size hypothesis.
      sorry
end CountingMatroid.Analysis.BoundedRunPhase
