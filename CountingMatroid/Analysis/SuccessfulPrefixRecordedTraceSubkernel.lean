import CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass
import CountingMatroid.Analysis.ExchangeProposalGeometry

set_option autoImplicit false

/-!
The successful-path subkernel comparison for the actual finite suffix.
The reference path begins with the actual capped restart endpoint sublaw,
so this obligation does not require a warm restart estimate. Its proof must
retain adaptive consumption and rejection-cap failures; it remains open.
-/
namespace CountingMatroid.Analysis.SuccessfulPrefixRecordedTraceSubkernel

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.RecordedObservationTrajectory
open CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

/-- INTERNAL: Successful recorded-trace mass before vector packaging.
Abort executions contribute zero and the original finite suffix is retained.
TEXLINE: main.tex:1181-1187,1392-1421 -/
noncomputable def cappedRecordedTraceMass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (states : List.Vector (PairedSet n) s.observations) : ℝ := by
  classical
  exact ∑ suffix : List.Vector Bool t,
    if ∃ observed : ObservationCursor n,
      ((restartPhase r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false)
        s current.tables j current.bitCursor).val.bind
        (observePhaseTrace r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false)
          s (s.ρ ^ j) current.currentWeights)) = some (observed, states.val)
    then 1 / (2 : ℝ) ^ t else 0

/-- INTERNAL: Ideal recorded-path mass with the actual capped restart
endpoint marginal in place of the stationary initial law. The final unused
transition is summed out exactly as in the parent's stationary projection.
TEXLINE: main.tex:1207-1212,1241-1255 -/
noncomputable def restartRecordedMass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (states : List.Vector (PairedSet n) s.observations) : ℝ := by
  classical
  exact ∑ path : Fin (s.observations + 1) → PairedSet n,
    if List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val then
      restartSuffixMass r o₁ o₂ s j current pref t (path 0) *
        ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ) else 0

/-- INTERNAL: The actual completed finite-suffix observation sublaw is
bounded by ideal transitions from the actual restart endpoint marginal.
This statement contains no warm-law hypothesis; that independent estimate
is used only by the parent after this comparison.
TEXLINE: main.tex:746-751,1181-1187,1207-1212,1392-1421 -/
theorem successful_prefix_recorded_trace_subkernel (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a)
    (hfixed : ∀ suffix : List.Vector Bool
        (CountingMatroid.Model.Run.blockLength n r p - pref.length),
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) j = some current)
    (states : List.Vector (PairedSet n)
      (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    cappedRecordedTraceMass r o₁ o₂ s j current pref t states ≤
      restartRecordedMass r o₁ o₂ s j current pref t
        (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn hq hw) states := by
  classical
  dsimp only
  unfold cappedRecordedTraceMass restartRecordedMass
  -- Concrete route: disintegrate the suffix at successful restart stopping
  -- prefixes, then induct over the recordedObservationTrace loop. The
  -- sibling observation_round_draw_site_covered supplies coverage once
  -- its owner publishes it (its imported DrawSites object is missing). The remaining
  -- bridge must give the joint successful value/cursor law for each
  -- boundedUniform call and chainStep, retaining stopping-prefix locality.
  -- A sum_le_sum comparison of individual suffix atoms cannot work:
  -- an individual deterministic transition need not have probability one
  -- under idealChain. The atom family must first be grouped by consumed
  -- prefixes. BoundedUniformAbortMass bounds failures, not successful values.
  -- BLOCKER: successful adaptive boundedUniform value/cursor sublaws and
  -- their chainStep/recordedObservationTrace finite-suffix composition.
  sorry

end CountingMatroid.Analysis.SuccessfulPrefixRecordedTraceSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · retained · live handoff recorded-path-domination-20261008-wave1 was mechanically rejected. An independent stdin probe of Finset.sum_le_sum failed to unify the suffix-indexed and ideal-path-indexed sums; direct atom comparison requires regrouping at stopping prefixes first.

* 2026-10-08 · decomposed · exposed the actual trace event and ideal path sum; identified the separate observation coverage theorem (its DrawSites object is currently absent). The remaining operational comparison requires successful adaptive value/cursor subkernels, independent of the warm endpoint bound.
-/
