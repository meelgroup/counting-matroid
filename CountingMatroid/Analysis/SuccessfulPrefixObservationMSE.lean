import CountingMatroid.Analysis.FinitePhaseObservationMSE
import Arlib.Probability.FinDistFunctional
import CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

set_option autoImplicit false

/-!
A real finite probability law for the actual unused Boolean suffix, and its
exact masked-error expectation. The conditional quantitative bound reduces
to the stationary correlated-average estimate and completed finite-tape
trajectory domination in the two imported support files. Those quantitative
obligations remain open in those support files.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixObservationMSE

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open Arlib.Probability Arlib.Probability.FinDist

/-- INTERNAL: Uniform probability law on length-t Boolean suffixes, in the
same finite-real probability API used by IdealExchangeChain.
TEXLINE: main.tex:1207-1212,1392-1421 -/
noncomputable def fairSuffixLaw (t : ℕ) : FinDist (List.Vector Bool t) where
  p _ := 1 / (2 : ℝ) ^ t
  p_nonneg _ := by positivity
  p_sum := by
    simp only [Finset.sum_const, Finset.card_univ, card_vector,
      Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
    field_simp

/-- INTERNAL: The finite rational masked moment is exactly expectation
under the uniform real suffix law. This preserves every operational abort
and invariant check in observationSquaredError.
TEXLINE: main.tex:1253-1266,1392-1421 -/
theorem masked_moment_eq_expectation {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j t : ℕ)
    (pref : List Bool) (index : Observable n) :
    (((∑ suffix : List.Vector Bool t,
      observationSquaredError r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
      (2 : ℚ) ^ t : ℚ) : ℝ) =
      Ex (fairSuffixLaw t) (fun suffix =>
        (observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) := by
  push_cast
  simp only [Ex, fairSuffixLaw, ← Finset.mul_sum]
  ring

/-- INTERNAL: Masking makes every incomplete operational observation
contribute zero to the second moment, retaining cap aborts explicitly.
TEXLINE: main.tex:1253-1266,1392-1421 -/
theorem masked_error_zero_on_incomplete {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (index : Observable n)
    (hincomplete : ¬ ObservationCompleted r o₁ o₂ tape s j) :
    observationSquaredError r o₁ o₂ tape s j index = 0 := by
  classical
  cases hdata : phaseObservationData r o₁ o₂ tape s j with
  | none => simp only [observationSquaredError, hdata]
  | some pair =>
      rcases pair with ⟨current, observed⟩
      by_cases hg : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
          0 < s.observations
      · exact False.elim (hincomplete ⟨current, observed, hdata, hg.1, hg.2⟩)
      · simp only [observationSquaredError, hdata, if_neg hg]

/-- INTERNAL: Restrict the actual fair-suffix expectation to completed
observation outputs. This is the exact subprobability quantity to dominate
by the corresponding uncapped trajectory squared error.
TEXLINE: main.tex:1253-1266,1392-1421 -/
theorem masked_expectation_eq_completed_sum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j t : ℕ)
    (pref : List Bool) (index : Observable n) :
    letI := Classical.propDecidable
    Ex (fairSuffixLaw t) (fun suffix =>
      (observationSquaredError r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) =
      ∑ suffix ∈ Finset.univ.filter (fun suffix : List.Vector Bool t =>
        ObservationCompleted r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j),
        fairSuffixLaw t suffix *
          (observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) := by
  classical
  dsimp only [Ex]
  symm
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro suffix _ hnot
  have hincomplete : ¬ ObservationCompleted r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j := by
    simpa only [Finset.mem_filter, Finset.mem_univ, true_and] using hnot
  rw [masked_error_zero_on_incomplete r o₁ o₂ _ s j index hincomplete]
  simp only [Rat.cast_zero, mul_zero]

/-- INTERNAL: The actual masked observation moment after a fixed successful
consumed prefix has the paper's warm time-average bound. Conditioning fixes
all stored kernels; the statement does not assume independent observations.
Abort mass is controlled separately by SuccessfulPrefixAbortBound.
TEXLINE: main.tex:952-1011,1207-1266,1392-1421 -/
theorem conditional_successful_prefix_observation_mse (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (index : Observable n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (∑ suffix : List.Vector Bool t,
      observationSquaredError r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
      (2 : ℚ) ^ t ≤ 40000 * (n : ℚ) ^ 8 / s.observations := by
  classical
  dsimp only
  apply (Rat.cast_le (K := ℝ)).mp
  rw [masked_moment_eq_expectation, masked_expectation_eq_completed_sum]
  obtain ⟨current, hw, hgood, hdom⟩ :=
    SuccessfulPrefixTrajectoryDomination.successful_prefix_trajectory_domination
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix index
  have hstat := StationaryObservableMSE.stationary_observation_mse
    n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ j current hgood hw index
  calc
    _ ≤ (10 * (n : ℝ) ^ 2) *
        StationaryObservableMSE.stationaryObservationMoment
          n r o₁ o₂ p hn j current hw index := hdom
    _ ≤ (10 * (n : ℝ) ^ 2) * (4000 * (n : ℝ) ^ 6 /
        (CountingMatroid.Interface.Pseudocode.setup n p).observations) :=
      mul_le_mul_of_nonneg_left hstat (by positivity)
    _ = ((40000 * (n : ℚ) ^ 8 /
        (CountingMatroid.Interface.Pseudocode.setup n p).observations : ℚ) : ℝ) := by
      push_cast
      ring

end CountingMatroid.Analysis.SuccessfulPrefixObservationMSE

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r24 · blocked · second live handoff `r24-stationary-mse-and-prefix-domination-2` was mechanically rejected without further diagnostic after all three modules built; retained the quantitative children with explicit covariance/resolvent and operational trajectory-domination blockers. The parent reduction moves proof debt and is not a completed quantitative proof.

* r24 · retained · live handoff `r24-stationary-mse-and-prefix-domination-1` was mechanically rejected without further diagnostic; the two quantitative child obligations remain owned here, and the checked parent reduction does not close their proof debt.

* r24 · decomposed · reduced the conditional MSE to stationary correlated-average MSE and completed finite-suffix trajectory domination; proved strict positivity and the real/rational observable-mean bridge in the stationary support file.

* r23 · reduced · proved masking vanishes on incomplete outputs and the exact sum over completed suffixes; neither identity supplies warm trajectory domination or covariance decay.

* r23 · attempted · constructed the real uniform suffix law and identified its exact masked expectation; warm operational trajectory domination and correlated-average MSE remain open.
-/
