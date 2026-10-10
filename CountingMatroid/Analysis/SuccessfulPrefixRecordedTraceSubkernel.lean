import CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass
import CountingMatroid.Analysis.ExchangeProposalGeometry
import CountingMatroid.Analysis.CoveredChainStepSubkernel
import CountingMatroid.Analysis.PhaseObservationBitCoverage
import CountingMatroid.Analysis.StoppedRecordedTraceSubkernel
import CountingMatroid.Analysis.SuccessfulPrefixCursor
import CountingMatroid.Analysis.RestartPhaseIntervalReplay

set_option autoImplicit false

/-!
The successful-path subkernel comparison for the actual finite suffix.
The reference path begins with the actual capped restart endpoint sublaw,
so this obligation does not require a warm restart estimate. Its proof must
retain adaptive consumption and rejection-cap failures. The covered one-step
comparison is isolated in CoveredChainStepSubkernel. Both restart-result
fiber identities and the aborted-restart case are proved. The parent composes
the deterministic finite-block coverage with the stopped-prefix composition
obligation in StoppedRecordedTraceSubkernel; the latter remains open.
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


/-- INTERNAL: Disintegrate the actual completed-trace event by its complete
restart result, retaining the returned cursor as well as the state.
This finite regrouping is exact and makes no stochastic assertion.
TEXLINE: main.tex:1181-1187,1207-1212,1392-1421 -/
theorem capped_recorded_trace_mass_restart_fibers {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (states : List.Vector (PairedSet n) s.observations) :
    by
    classical
    let R := fun suffix : List.Vector Bool t =>
      (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
        s current.tables j current.bitCursor).val
    exact cappedRecordedTraceMass r o₁ o₂ s j current pref t states =
      ∑ outcome ∈ Finset.univ.image R, ∑ suffix : List.Vector Bool t,
        if R suffix = outcome ∧ ∃ observed : ObservationCursor n,
          outcome.bind (observePhaseTrace r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false)
            s (s.ρ ^ j) current.currentWeights) = some (observed, states.val)
        then 1 / (2 : ℝ) ^ t else 0 := by
  classical
  dsimp only
  unfold cappedRecordedTraceMass
  let R := fun bits : List.Vector Bool t =>
    (restartPhase r o₁ o₂ (fun i => ((pref ++ bits.val)[i]?).getD false)
      s current.tables j current.bitCursor).val
  let E := fun (bits : List.Vector Bool t) (outcome : Option (PairedSet n × ℕ)) =>
    ∃ observed : ObservationCursor n,
      outcome.bind (observePhaseTrace r o₁ o₂
        (fun i => ((pref ++ bits.val)[i]?).getD false)
        s (s.ρ ^ j) current.currentWeights) = some (observed, states.val)
  change (∑ suffix : List.Vector Bool t, if E suffix (R suffix) then 1 / (2 : ℝ) ^ t else 0) =
    ∑ outcome ∈ Finset.univ.image R, ∑ suffix : List.Vector Bool t,
      if R suffix = outcome ∧ E suffix outcome then 1 / (2 : ℝ) ^ t else 0
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro suffix _
  have hmem : R suffix ∈ Finset.univ.image R :=
    Finset.mem_image_of_mem _ (Finset.mem_univ suffix)
  have hterm (outcome : Option (PairedSet n × ℕ)) :
      (if R suffix = outcome ∧ E suffix outcome then 1 / (2 : ℝ) ^ t else 0) =
      if R suffix = outcome then
        (if E suffix (R suffix) then 1 / (2 : ℝ) ^ t else 0) else 0 := by
    by_cases heq : R suffix = outcome
    · subst outcome
      simp only [true_and, if_true]
    · simp only [heq, false_and, if_false]
  simp_rw [hterm]
  simp only [Finset.sum_ite_eq, hmem, if_true]


/-- INTERNAL: The ideal path mixture has the same restart-result fibers as
the actual trace event. Its path factor depends only on the returned state;
the restart marginal still retains the full result and its adaptive cursor.
TEXLINE: main.tex:1181-1187,1207-1212,1392-1421 -/
theorem restart_recorded_mass_restart_fibers {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (states : List.Vector (PairedSet n) s.observations) :
    by
    classical
    let R := fun suffix : List.Vector Bool t =>
      (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
        s current.tables j current.bitCursor).val
    exact restartRecordedMass r o₁ o₂ s j current pref t P states =
      ∑ outcome ∈ Finset.univ.image R,
        (∑ suffix : List.Vector Bool t,
          if R suffix = outcome then 1 / (2 : ℝ) ^ t else 0) *
        ∑ path : Fin (s.observations + 1) → PairedSet n,
          if List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val ∧
            outcome.map Prod.fst = some (path 0)
          then ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ) else 0 := by
  classical
  dsimp only
  let R := fun bits : List.Vector Bool t =>
    (restartPhase r o₁ o₂ (fun i => ((pref ++ bits.val)[i]?).getD false)
      s current.tables j current.bitCursor).val
  let C := fun path : Fin (s.observations + 1) → PairedSet n =>
    List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val
  let G := fun path : Fin (s.observations + 1) → PairedSet n =>
    ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ)
  let Q := fun outcome : Option (PairedSet n × ℕ) =>
    ∑ path : Fin (s.observations + 1) → PairedSet n,
      if C path ∧ outcome.map Prod.fst = some (path 0) then G path else 0
  have hpath : restartRecordedMass r o₁ o₂ s j current pref t P states =
      ∑ suffix : List.Vector Bool t, (1 / (2 : ℝ) ^ t) * Q (R suffix) := by
    unfold restartRecordedMass restartSuffixMass
    change (∑ path : Fin (s.observations + 1) → PairedSet n,
      if C path then
        (∑ suffix : List.Vector Bool t,
          if (R suffix).map Prod.fst = some (path 0) then 1 / (2 : ℝ) ^ t else 0) *
        G path else 0) = _
    have hterm (path : Fin (s.observations + 1) → PairedSet n) :
        (if C path then
          (∑ suffix : List.Vector Bool t,
            if (R suffix).map Prod.fst = some (path 0) then 1 / (2 : ℝ) ^ t else 0) *
          G path else 0) =
        ∑ suffix : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
          (if C path ∧ (R suffix).map Prod.fst = some (path 0) then G path else 0) := by
      by_cases hc : C path
      · simp only [hc, true_and, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro suffix _
        split_ifs <;> simp only [mul_zero, zero_mul]
      · simp only [hc, false_and, if_false, mul_zero, Finset.sum_const_zero]
    simp_rw [hterm]
    rw [Finset.sum_comm]
    simp only [Q, Finset.mul_sum]
  rw [hpath]
  change _ = ∑ outcome ∈ Finset.univ.image R,
    (∑ suffix : List.Vector Bool t, if R suffix = outcome then 1 / (2 : ℝ) ^ t else 0) * Q outcome
  symm
  simp_rw [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro suffix _
  have hmem : R suffix ∈ Finset.univ.image R :=
    Finset.mem_image_of_mem _ (Finset.mem_univ suffix)
  simp only [Finset.sum_ite_eq, hmem, if_true]


/-- Keep finite regrouping and stopped-prefix composition generic so kernel
checking does not repeatedly unfold the concrete schedule and bit budget. -/
private theorem recorded_subkernel_of_coverage {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (u : ℕ) (state next : PairedSet n),
      state.card = n → (classifyState state).val ≠ .invalid →
      CoveredChainStepSubkernel.coveredChainStepMass r o₁ o₂ s.drawTrials
        (s.ρ ^ j) current.currentWeights head u state next ≤ P state next)
    (hreplay : ChainStepIntervalReplay.SuccessReplay
      (fun tape => (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val)
      Prod.snd pref.length)
    (htrans : ∀ tape result,
      (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val = some result →
      (classifyState result.1).val = .transversal)
    (hcovered : ∀ (suffix : List.Vector Bool t) result observed recorded,
      (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
        s current.tables j current.bitCursor).val = some result →
      observePhaseTrace r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
        s (s.ρ ^ j) current.currentWeights result = some (observed, recorded) →
      observed.bitCursor ≤ pref.length + t)
    (states : List.Vector (PairedSet n) s.observations) :
    cappedRecordedTraceMass r o₁ o₂ s j current pref t states ≤
      restartRecordedMass r o₁ o₂ s j current pref t P states := by
  classical
  rw [capped_recorded_trace_mass_restart_fibers,
    restart_recorded_mass_restart_fibers]
  apply Finset.sum_le_sum
  intro outcome _
  cases outcome with
  | none =>
      simp only [Option.bind_none, Option.map_none, reduceCtorEq, exists_false,
        and_false, if_false, Finset.sum_const_zero, mul_zero]
      exact le_rfl
  | some start =>
    have hbound := StoppedRecordedTraceSubkernel.stopped_recorded_trace_subkernel
      r o₁ o₂ s (s.ρ ^ j) current.currentWeights pref t
      (fun tape => (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val)
      hreplay htrans hcovered P hstep start states
    simpa only [Option.bind_some, Option.map_some, Option.some.injEq] using hbound


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
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let t := m - pref.length
  let initialRun := fun tape : ℕ → Bool =>
    (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val
  obtain ⟨bits, original, hbits, _, horiginal, _, hpref, hprefLength⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor
      n r o₁ o₂ p j hj pref hprefix
  have hp : pref <+: bits := hpref ▸ List.take_prefix _ _
  have hconcat : pref ++ bits.drop pref.length = bits :=
    (List.prefix_append_drop hp).symm
  let originalSuffix : List.Vector Bool t :=
    ⟨bits.drop pref.length, by simpa only [t, m, List.length_drop, hbits]⟩
  have hsame := hfixed originalSuffix
  change BoundedRunPhaseHistory.phaseHistory r o₁ o₂
    (fun i => ((pref ++ bits.drop pref.length)[i]?).getD false) s j = some current at hsame
  rw [hconcat, horiginal] at hsame
  have heq : original = current := Option.some.inj hsame
  have hstart : pref.length ≤ current.bitCursor := by
    rw [hprefLength, ← heq]
    exact Nat.min_le_left _ _
  have hlen : pref.length ≤ m := by
    rw [hprefLength]
    exact Nat.min_le_right _ _
  have hreplay : ChainStepIntervalReplay.SuccessReplay initialRun Prod.snd pref.length := by
    intro tape result hrun
    have hrp := RestartPhaseIntervalReplay.restartPhase_success_interval
      r o₁ o₂ s current.tables j current.bitCursor tape result hrun
    refine ⟨hstart.trans hrp.1, ?_⟩
    intro other hagree
    exact hrp.2 other (fun i hlo hhi => hagree i (hstart.trans hlo) hhi)
  have htrans : ∀ tape result, initialRun tape = some result →
      (classifyState result.1).val = .transversal := by
    intro tape result hrun
    exact RestartPhaseTransversal.restartPhase_transversal
      r o₁ o₂ tape s current.tables j current.bitCursor result hrun
  have hcovered : ∀ (suffix : List.Vector Bool t) result observed recorded,
      initialRun (fun i => ((pref ++ suffix.val)[i]?).getD false) = some result →
      observePhaseTrace r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
        s (s.ρ ^ j) current.currentWeights result = some (observed, recorded) →
      observed.bitCursor ≤ pref.length + t := by
    intro suffix result observed recorded hrestart htrace
    have hobserve := recorded_trace_observePhase r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s
      (s.ρ ^ j) current.currentWeights result
    rw [htrace] at hobserve
    have hbound := PhaseObservationBitCoverage.phase_observation_cursor_le_block
      n r o₁ o₂ p hn (fun i => ((pref ++ suffix.val)[i]?).getD false)
      j hj current result observed (hfixed suffix) hrestart hobserve.symm
    simpa only [t, Nat.add_sub_of_le hlen] using hbound
  apply recorded_subkernel_of_coverage r o₁ o₂ s j current pref t
    (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j) current.currentWeights
      hn (pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j) hw)
    ?_ hreplay htrans hcovered states
  intro head u state next hcard hvalid
  exact CoveredChainStepSubkernel.covered_chain_step_subkernel r o₁ o₂ s.drawTrials
    (s.ρ ^ j) current.currentWeights hn
    (pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j)
    hw head u state next hcard hvalid

end CountingMatroid.Analysis.SuccessfulPrefixRecordedTraceSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · compiler maintenance · moved finite regrouping and stopped-prefix composition into a generic schedule/suffix helper. The public statement and stochastic obligations are unchanged; this avoids repeated concrete-schedule reduction during kernel checking.

* 2026-10-09 · reduced · proved deterministic full observation bit coverage in PhaseObservationBitCoverage; instantiated the generic stopped recorded-trace comparison with exact restart replay, transversal return, and original-history cursor extraction. The remaining positive-length stochastic composition is in StoppedRecordedTraceSubkernel; this moves, rather than closes, that proof obligation.

* 2026-10-09 · deferred handoff · fresh wave2 was deferred for the active TransversalVarianceBound writer in the producer build closure; statements and parent/child source checks are verified, but no child ownership has transferred. Preserve the decomposition for automatic settled-boundary revalidation.

* 2026-10-09 · proved reduction · both exact restart-result fiber identities check, and the aborted-restart fiber closes at zero. Direct hstep application to a successful restart fiber fails because the goal is a whole-trace joint bound; stopped-prefix disintegration and trace induction remain. Live child handoff wave1 was deferred for the active SuccessfulPrefixRestartEndpointMass writer; ownership retained.

* 2026-10-09 · decomposed · parent applies the covered one-step subkernel child through its continuation invariant; remaining parent proof is stopping-prefix disintegration and trace induction. Rechecked that observation draw coverage is proved; the earlier missing-object note no longer applies.

* 2026-10-08 · retained · live handoff recorded-path-domination-20261008-wave1 was mechanically rejected. An independent stdin probe of Finset.sum_le_sum failed to unify the suffix-indexed and ideal-path-indexed sums; direct atom comparison requires regrouping at stopping prefixes first.

* 2026-10-08 · decomposed · exposed the actual trace event and ideal path sum; identified the separate observation coverage theorem (its DrawSites object is currently absent). The remaining operational comparison requires successful adaptive value/cursor subkernels, independent of the warm endpoint bound.
-/
