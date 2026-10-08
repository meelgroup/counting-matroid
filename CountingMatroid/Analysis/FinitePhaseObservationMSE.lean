import CountingMatroid.Analysis.StationaryMeanLowerBound

set_option autoImplicit false

/-!
Normalization of the actual finite-tape observation second moment. The live
handoff of its quantitative estimate was mechanically rejected. This module
asserts only the proved denominator-clearing equivalence; the trajectory MSE
estimate remains a local obligation of `finite_tape_lower_tail_bound`.
-/

namespace CountingMatroid.Analysis.FinitePhaseObservationMSE

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Normalize the concrete successful-observation second moment to
a finite sum inequality. This does not assert mixing or concentration.
TEXLINE: main.tex:1207-1266,1392-1421 -/
theorem conditional_phase_observation_mse_iff (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (pref : List Bool) (index : Observable n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let moment := ∑ suffix : List.Vector Bool t,
      observationSquaredError r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index
    moment / (2 : ℚ) ^ t ≤ 40000 * (n : ℚ) ^ 8 / s.observations ↔
      moment ≤ (40000 * (n : ℚ) ^ 8 / s.observations) * (2 : ℚ) ^ t := by
  dsimp only
  exact div_le_iff₀ (by positivity)

end CountingMatroid.Analysis.FinitePhaseObservationMSE

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r22 · rejected handoff · `r22-conditional-abort-mse-1` was mechanically
  rejected without diagnostic. The attempted finite-disintegration route
  exposed the sum of actual masked deviations, requiring an ideal trajectory,
  warm endpoint domination and time-average MSE, followed by finite-block
  coupling. Retained the proved normalization and kept the estimate local
  to the assigned parent, rather than exporting an unfinished theorem.
-/
