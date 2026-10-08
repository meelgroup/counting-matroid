import CountingMatroid.Analysis.StationaryObservableMSE
import CountingMatroid.Analysis.SuccessfulPrefixAbortBound

set_option autoImplicit false

/-!
The operational coupling needed for a successful consumed prefix: completed
finite-tape observation errors are dominated by 10 n² times the stationary
ideal trajectory moment at a single fixed good phase cursor. This does not
assert the stationary time-average estimate; that is a separate obligation.
The prefix-to-trajectory domination remains open.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE

/-- INTERNAL: Couple completed executions after a successful consumed prefix
to a fixed stationary ideal trajectory, retaining every operational abort.
The 10 n² factor is the paper's uncapped restart endpoint domination; neither
independent observations nor an alternative bit source is assumed.
TEXLINE: main.tex:1207-1255,1392-1421 -/
theorem successful_prefix_trajectory_domination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (index : Observable n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    letI := Classical.propDecidable
    ∃ (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a),
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
      (∑ suffix ∈ Finset.univ.filter (fun suffix : List.Vector Bool t =>
        ObservationCompleted r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j),
        (1 / (2 : ℝ) ^ t) *
          (observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) ≤
        (10 * (n : ℝ) ^ 2) *
          stationaryObservationMoment n r o₁ o₂ p hn j current hw index := by
  classical
  obtain ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, hprefLength⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor
      n r o₁ o₂ p j hj pref hprefix
  let m := CountingMatroid.Model.Run.blockLength n r p
  have hplen : pref.length ≤ m := by
    rw [hprefLength]
    exact Nat.min_le_right _ _
  have hfullLength (suffix : List.Vector Bool (m - pref.length)) :
      (pref ++ suffix.val).length = m := by
    rw [List.length_append, suffix.property]
    omega
  let hw := good_current_weights_pos n r o₁ o₂ p hn j current hstored
  refine ⟨current, hw, hstored, ?_⟩
  -- Attempt: the actual certified history supplies this fixed good cursor,
  -- and positivity permits its concrete ideal kernel. The exact prefix length
  -- is only min current.bitCursor blockLength, so replay on completed suffixes
  -- requires a cursor/denominator coverage bound before fresh-bit domination.
  -- After replay, identify recordObservation with operationalObservable along
  -- the path and dominate the capped restart endpoint by the uncapped law
  -- ≤ 2 μ_j ≤ 10 n² π. There is no operational transition/trace law theorem
  -- in the current imports that supplies this comparison.
  -- A second stdin attempt with aesop exhausted its search and left exactly
  -- this moment-domination inequality for both Boolean and pair indices.
  -- BLOCKER: finite-block replay and capped-to-ideal trajectory domination,
  -- including the trace endpoint mixing estimate at main.tex:1214-1240.
  sorry

end CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r24 · open · extracted the reached good cursor and proved full completed-tape length; aesop left the exact moment-domination inequality, without any trajectory-law comparison in the hypotheses. The first live child handoff was mechanically rejected without further diagnostic.
-/
