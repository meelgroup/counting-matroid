import CountingMatroid.Analysis.SingleRunAccuracy

set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- PAPER: main.tex:1442-1462
Independent bounded runs with one-run failure at most one quarter give the
requested confidence after the paper's scheduled median repetitions. -/
theorem median_amplification_bound (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (lower upper : ℚ)
    (hpretest : CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ = none)
    (hrun :
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let runLaw :=
        (CountingMatroid.Model.Run.fairTape
          (CountingMatroid.Model.Run.blockLength n r p)).map
          (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
            (fun i => (bits[i]?).getD false) s)
      runLaw.toOuterMeasure {y : ℚ | y < lower ∨ upper < y} ≤
        (1 / 4 : ENNReal)) :
    (CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p).toOuterMeasure
      {y : ℚ | y < lower ∨ upper < y} ≤ ENNReal.ofReal (p.δ : ℝ) := by
  -- Unfolding exposes the finite product of independent blocks, followed by
  -- the median. The remaining step is the product/Markov estimate.
  unfold CountingMatroid.Interface.Pseudocode.estimateLaw
  simp only [CountingMatroid.Interface.Pseudocode.estimate, hpretest]
  change (PMF.map
    (fun blocks => CountingMatroid.Interface.Pseudocode.median
      ((List.range (CountingMatroid.Interface.Pseudocode.setup n p).repetitions).map
        (fun j => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (CountingMatroid.Model.Run.blockTape blocks j)
          (CountingMatroid.Interface.Pseudocode.setup n p))))
    (CountingMatroid.Model.Run.fairBlocks
      (CountingMatroid.Interface.Pseudocode.setup n p).repetitions
      (CountingMatroid.Model.Run.blockLength n r p))).toOuterMeasure
      {y : ℚ | y < lower ∨ upper < y} ≤ ENNReal.ofReal (p.δ : ℝ)
  rw [PMF.toOuterMeasure_map_apply]
  sorry

end CountingMatroid.Analysis.MedianAmplification
