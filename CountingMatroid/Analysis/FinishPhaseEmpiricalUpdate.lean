import CountingMatroid.Model.Program

set_option autoImplicit false

namespace CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Exact empirical update computed by the successful finish scan.
The formula uses the original multiplier once for each off-diagonal index;
normalizing both counts by the observation count cancels.
TEXLINE: main.tex:1181-1201,1257-1270 -/
noncomputable def empiricalWeights {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n) : Multipliers n :=
  fun index => if j + 1 < s.L then
    weights index * (observed.counts .transversal : ℚ) /
      (observed.counts (.defect index.emptyPair index.fullPair) : ℚ)
    else weights index

/-- INTERNAL: Positive empirical type counts make the actual nested finishing
scan succeed, with precisely the ratio and multiplier updates of the paper.
This is a deterministic statement, including an empty defect-index family.
TEXLINE: main.tex:1181-1201 -/
theorem finishPhase_empirical_update {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (hN : 0 < s.observations) (hzero : 0 < observed.counts .transversal)
    (hdefect : ∀ index : DefectIndex n,
      0 < observed.counts (.defect index.emptyPair index.fullPair)) :
    (finishPhase s j weights observed).val =
      some (observed.numeratorSum / (observed.counts .transversal : ℚ),
        empiricalWeights s j weights observed) := by
  -- Concrete route: unfold the charged operations to obtain two finite
  -- folds over List.finRange n. Positive counts eliminate every abort.
  -- The remaining invariant must record which off-diagonal indices have
  -- been visited: their entry has its empirical update, and every unvisited
  -- entry still has its ORIGINAL weight. Positivity alone does not prove
  -- the formula, since applying a scalar update twice changes its value.
  -- List.nodup_finRange provides exactly-once visitation in each scan.
  -- Normalization cancellation then needs hN and hzero, both supplied here.
  sorry

end CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate
