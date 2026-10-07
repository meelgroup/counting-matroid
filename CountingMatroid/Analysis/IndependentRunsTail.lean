import CountingMatroid.Analysis.IndependentRunsCore

set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: The finite product tail estimate for a strict majority of bad runs.
TEXLINE: main.tex:1448-1458 -/
theorem independent_runs_majority_tail (q : PMF ℚ) (bad : ℚ → Bool) (b : ℕ)
    (hq : q.toOuterMeasure {x | bad x = true} ≤ (1 / 4 : ENNReal)) :
    (independentRuns q (10 * b + 1)).toOuterMeasure
      {xs | (10 * b + 1) / 2 + 1 ≤ xs.countP bad} ≤
      (1 / 2 : ENNReal) ^ b := by
  -- The intended proof uses the bind expansion of `independentRuns`, the
  -- exponential moment of the failure count, and Markov's inequality.
  sorry

end CountingMatroid.Analysis.MedianAmplification
