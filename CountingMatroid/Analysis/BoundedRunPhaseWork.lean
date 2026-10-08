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
      rcases hacc current rfl with ⟨hweights, htables, hproduct⟩
      unfold boundedRunPhase
      rw [CountingMatroid.Analysis.ResourceBound.otherSteps_bind,
        CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
      -- BLOCKER (dependency placement): the first summand is
      -- otherSteps (ratPower s.ρ j). The existing theorem
      -- BoundedRunResourceEnvelope.ratPower_otherSteps_le bounds it by
      -- j * (binaryRatLength 1 + j * binaryRatLength s.ρ)^2, without any
      -- positivity hypothesis. Its module imports BoundedRunOtherSteps,
      -- which imports this file, so importing it here creates a cycle.
      -- ratPower_binary_length_le and observePhase_counts_le have the same
      -- placement problem; observePhase_height_le and
      -- finishPhase_ratio_length_le are additionally private there.
      -- Extract that existing power/count/height support into an upstream
      -- module before using it here; do not duplicate the proved declarations.
      -- BLOCKER (remaining local work): the other summands require bounds
      -- for restartPhase (including traceReturn/chainStep and capped draws),
      -- observePhase (including the growing accumulator), and finishPhase
      -- (including intermediate multiplier sizes in its nested scan).
      -- No nonoracle-cost bounds for these subroutines were found in Analysis.
      -- The input bounds hweights/htables/hproduct alone do not bound arbitrary
      -- scan accumulators. A stdin probe of otherSteps_foldl_le_of_mem on
      -- ratPower produces a multiplication-cost goal for every acc : ℚ,
      -- losing precisely the reached-value size invariant.
      sorry
end CountingMatroid.Analysis.BoundedRunPhase

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · blocked · confirmed the upstream cost decomposition and unpacked the input size invariant; existing power/count/height support is downstream of this file, and the uniform-fold probe loses the reached-accumulator size bound. No new proof debt was introduced.
-/
