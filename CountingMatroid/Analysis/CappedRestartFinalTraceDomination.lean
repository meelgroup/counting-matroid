import CountingMatroid.Analysis.IdealExchangeChain
import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.PositiveTimeTraceKernel
import CountingMatroid.Analysis.RestartSuffixMassDefinition
import CountingMatroid.Analysis.RestartPhaseIntervalReplay

import CountingMatroid.Analysis.CappedTraceIterationSubkernel
import CountingMatroid.Analysis.RestartPhaseBitCoverage
import CountingMatroid.Analysis.SuccessfulPrefixCursor
import CountingMatroid.Analysis.CoveredChainStepSubkernel
import CountingMatroid.Analysis.RecordedTraceContinuationBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The last-stage finite-suffix comparison for a successful phase prefix. Its
reference starts with the actual preceding-stage sublaw and grants each final
trace return the full cap, which can only add mass relative to the shared
operational attempt cap. Stopped-prefix disintegration, positive-time return
composition, and deterministic finite-block coverage prove the comparison.
-/
namespace CountingMatroid.Analysis.CappedRestartFinalTraceDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: The actual restart stage, retaining its phase-global attempt
counter and its absorbing abort state.
TEXLINE: main.tex:1163-1176 -/
def restart_stage {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (index : ℕ) (current : Option (RestartCursor n)) :
    Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
      (Option (RestartCursor n)) := do
  match current with
  | none => pure none
  | some current =>
      let a ← Model.Operations.successor index
      let q ← ratPower s.ρ a
      let weights ← Model.Operations.learnedWeightRead tables a s.L
      Arlib.Computation.Charged.repeatFor (fun _ acc => do
        match acc with
        | none => pure none
        | some acc => traceReturn r o₁ o₂ tape s q weights acc)
        s.τ (some current)

/-- INTERNAL: The internal restart result before projecting away its attempt
counter. This is the same fresh scan and nested loop as `restartPhase`.
TEXLINE: main.tex:1163-1176 -/
noncomputable def restart_phase_cursor {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) : Option (RestartCursor n) :=
  let initial := (freshTransversal n tape cursor).val
  (Arlib.Computation.Charged.repeatFor (fun index current =>
    restart_stage r o₁ o₂ tape s tables index current)
    j (some ⟨initial.1, initial.2, 0⟩)).val

/-- INTERNAL: A charged list fold splits without discarding the prefix value. -/
private theorem cursor_fold_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Restore exactly the public state/cursor result from the internal
restart, including every abort branch.
TEXLINE: main.tex:1163-1176 -/
theorem restart_phase_cursor_projection {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ) :
    (restartPhase r o₁ o₂ tape s tables j cursor).val =
      (restart_phase_cursor r o₁ o₂ tape s tables j cursor).map
        (fun out => (out.state, out.bitCursor)) := by
  unfold restartPhase restart_phase_cursor
  simp only [Arlib.Computation.Charged.val_bind]
  change (match (Arlib.Computation.Charged.repeatFor
    (fun index current => restart_stage r o₁ o₂ tape s tables index current)
    j (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩)).val with
    | none => pure none
    | some out => pure (some (out.state, out.bitCursor)) :
      Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
        (Option (PairedSet n × ℕ))).val = _
  cases (Arlib.Computation.Charged.repeatFor
    (fun index current => restart_stage r o₁ o₂ tape s tables index current)
    j (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩)).val <;> rfl

/-- INTERNAL: Split off the final stage without resetting the shared attempts
counter, drawing a second initial transversal, or forgetting the stopping cursor.
TEXLINE: main.tex:1163-1176 -/
theorem restart_phase_cursor_succ {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ) :
    restart_phase_cursor r o₁ o₂ tape s tables (j + 1) cursor =
      (restart_stage r o₁ o₂ tape s tables j
        (restart_phase_cursor r o₁ o₂ tape s tables j cursor)).val := by
  unfold restart_phase_cursor
  simp only [Arlib.Computation.Charged.repeatFor]
  rw [List.range_succ, cursor_fold_append]
  rfl

/-- INTERNAL: The final stage retains the interval replay of all its positive
time returns, including the shared attempt counter in the result.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_stage_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (tables : LearnedWeights n) (index : ℕ) (current : RestartCursor n) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => (restart_stage r o₁ o₂ tape s tables index (some current)).val)
      RestartCursor.bitCursor current.bitCursor := by
  unfold restart_stage
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
  apply ChainStepIntervalReplay.foldl_successReplay
  · intro tape index
    rfl
  · intro acc index
    exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s _ _ acc

/-- INTERNAL: Full restart cursors, including the global attempt count, replay
from the interval consumed by the fresh scan and all preceding stages.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_phase_cursor_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (tables : LearnedWeights n) (j start : ℕ) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => restart_phase_cursor r o₁ o₂ tape s tables j start)
      RestartCursor.bitCursor start := by
  let cross := fun tape current =>
    (Arlib.Computation.Charged.foldl
      (fun acc index => restart_stage r o₁ o₂ tape s tables index acc)
      (List.range j) (some current)).val
  have hcross : ∀ current, ChainStepIntervalReplay.SuccessReplay
      (fun tape => cross tape current) RestartCursor.bitCursor current.bitCursor := by
    intro current
    apply ChainStepIntervalReplay.foldl_successReplay
    · intro tape a
      rfl
    · intro acc index
      exact restart_stage_success_interval r o₁ o₂ s tables index acc
  intro tape out hrun
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape start).val.1, (freshTransversal n tape start).val.2, 0⟩
  change cross tape initial = some out at hrun
  have hlocal := hcross initial tape out hrun
  have hinit : initial.bitCursor = start + n := by
    simp only [initial, InitialRestartLaw.freshTransversal_value]
  have hstart : start ≤ initial.bitCursor := by rw [hinit]; omega
  refine ⟨hstart.trans hlocal.1, ?_⟩
  intro other hagree
  have hfresh : (freshTransversal n other start).val =
      (freshTransversal n tape start).val := by
    rw [InitialRestartLaw.freshTransversal_value, InitialRestartLaw.freshTransversal_value]
    congr 1
    apply Finset.image_congr
    intro i _
    change (i, other (start + i.val)) = (i, tape (start + i.val))
    congr 1
    exact (hagree (start + i.val) (by omega) (by
      have hi := i.isLt
      rw [hinit] at hlocal
      omega)).symm
  have heq := hlocal.2 other (fun i hlo hhi => hagree i (hstart.trans hlo) hhi)
  unfold restart_phase_cursor
  dsimp only
  rw [hfresh]
  exact heq

/-- INTERNAL: Expose a stage as the fold to which the covered trace-return
composition theorem applies. No attempt counter is reset.
TEXLINE: main.tex:1163-1176 -/
theorem restart_stage_eq_trace_fold {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (index : ℕ)
    (current : RestartCursor n) :
    (restart_stage r o₁ o₂ tape s tables index (some current)).val =
      CappedTraceIterationSubkernel.traceFold r o₁ o₂ tape s (s.ρ ^ (index+1))
        (tables (index+1)) (List.range s.τ) (some current) := by
  unfold restart_stage CappedTraceIterationSubkernel.traceFold
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, BoundedRunResourceEnvelope.ratPower_value,
    Model.Operations.learnedWeightRead, Arlib.Computation.Charged.val_opMany,
    Arlib.Computation.Charged.repeatFor]
  rfl

/-- INTERNAL: Express final-stage success using both full cursors and their
consumed interval. An aborted preceding stage cannot become successful.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_final_stage_event_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (index : ℕ)
    (initial : Option (RestartCursor n)) (state : PairedSet n) :
    ((restart_stage r o₁ o₂ tape s tables index initial).val).map RestartCursor.state =
        some state ↔
      ∃ start out : RestartCursor n, initial = some start ∧
        (restart_stage r o₁ o₂ tape s tables index (some start)).val = some out ∧
        out.state = state ∧ start.bitCursor ≤ out.bitCursor := by
  constructor
  · intro h
    cases initial with
    | none =>
        simp only [restart_stage, Arlib.Computation.Charged.val_pure, Option.map_none]
          at h
        cases h
    | some start =>
        obtain ⟨out, hout, hstate⟩ := Option.map_eq_some_iff.mp h
        exact ⟨start, out, rfl, hout, hstate,
          (restart_stage_success_interval r o₁ o₂ s tables index start tape out hout).1⟩
  · rintro ⟨start, out, hstart, hout, hstate, _⟩
    rw [hstart, hout, Option.map_some, hstate]

/-- INTERNAL: A stage containing zero trace transitions retains the whole
cursor, including its shared attempt count.
TEXLINE: main.tex:1163-1176 -/
theorem restart_stage_zero_trace {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (index : ℕ)
    (current : Option (RestartCursor n)) (hτ : s.τ = 0) :
    (restart_stage r o₁ o₂ tape s tables index current).val = current := by
  cases current <;>
    simp only [restart_stage, Arlib.Computation.Charged.val_bind, hτ,
      Arlib.Computation.Charged.repeatFor, List.range_zero,
      Arlib.Computation.Charged.val_foldl_nil, Arlib.Computation.Charged.val_pure]

/-- INTERNAL: If every stage has zero trace transitions, the restart is its
single fresh transversal scan, independently of the number of stages.
TEXLINE: main.tex:1163-1176 -/
theorem restart_phase_cursor_zero_trace {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (hτ : s.τ = 0) :
    restart_phase_cursor r o₁ o₂ tape s tables j cursor =
      some ⟨(freshTransversal n tape cursor).val.1,
        (freshTransversal n tape cursor).val.2, 0⟩ := by
  induction j with
  | zero => rfl
  | succ j ih =>
      rw [restart_phase_cursor_succ, restart_stage_zero_trace r o₁ o₂ tape s tables j _ hτ,
        ih]

/-- INTERNAL: Actual capped restart endpoint mass under a finite fair suffix.
This definition is shared with the parent's original public spelling.
TEXLINE: main.tex:1163-1176,1207-1212,1392-1421 -/
noncomputable def restartSuffixMass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (state : PairedSet n) : ℝ := by
  classical
  exact ∑ suffix : List.Vector Bool t,
    if ((restartPhase r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false)
      s current.tables j current.bitCursor).val).map Prod.fst = some state
    then 1 / (2 : ℝ) ^ t else 0

/-- INTERNAL: Expose the actual final-stage event before any probability
comparison. The preceding internal restart retains its remaining global cap.
TEXLINE: main.tex:1163-1176 -/
theorem restart_suffix_mass_final_stage {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (hj : 0 < j) (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (state : PairedSet n) :
    restartSuffixMass r o₁ o₂ s j current pref t state =
      ∑ suffix : List.Vector Bool t,
        if ((restart_stage r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s current.tables (j - 1)
          (restart_phase_cursor r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s current.tables (j - 1)
            current.bitCursor)).val).map RestartCursor.state = some state
        then 1 / (2 : ℝ) ^ t else 0 := by
  classical
  unfold restartSuffixMass
  apply Finset.sum_congr rfl
  intro suffix _
  have hsplit := restart_phase_cursor_succ r o₁ o₂
    (fun i => ((pref ++ suffix.val)[i]?).getD false) s current.tables (j - 1)
    current.bitCursor
  rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hj)] at hsplit
  rw [restart_phase_cursor_projection, hsplit, Option.map_map]
  rfl

/-- INTERNAL: Dominate the final operational restart stage by iterated
capped ideal positive-time returns, retaining the actual previous-stage mass.
The cap is granted afresh per ideal return, so no successful operational
restart is removed by the reference subkernel.
TEXLINE: main.tex:1163-1176,1207-1212,1392-1421 -/
theorem capped_restart_final_trace_domination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hjpos : 0 < j) (pref : List Bool)
    (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (htable : ∀ a, 0 < current.tables j a)
    (hfixed : ∀ suffix : List.Vector Bool
        (CountingMatroid.Model.Run.blockLength n r p - pref.length),
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) j = some current)
    (state : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
      (current.tables j) hn hq htable
    let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
    restartSuffixMass r o₁ o₂ s j current pref t state ≤
      ∑ x, restartSuffixMass r o₁ o₂ s (j - 1) current pref t x *
        (PositiveTimeTraceKernel.iterate
          (PositiveTimeTraceKernel.returnWithin P A s.restartCap) s.τ).entry x state := by
  classical
  dsimp only
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  by_cases hτ : s.τ = 0
  · have hmass : restartSuffixMass r o₁ o₂ s j current pref t state =
        restartSuffixMass r o₁ o₂ s (j - 1) current pref t state := by
      unfold restartSuffixMass
      apply Finset.sum_congr rfl
      intro suffix _
      rw [restart_phase_cursor_projection, restart_phase_cursor_projection,
        restart_phase_cursor_zero_trace r o₁ o₂ _ s current.tables j current.bitCursor hτ,
        restart_phase_cursor_zero_trace r o₁ o₂ _ s current.tables (j - 1)
          current.bitCursor hτ]
    change restartSuffixMass r o₁ o₂ s j current pref t state ≤ _
    simp only [show (CountingMatroid.Interface.Pseudocode.setup n p).τ = 0 from hτ,
      PositiveTimeTraceKernel.iterate, PositiveTimeTraceKernel.identity]
    simpa only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
      if_true] using hmass.le
  have hν := SuccessfulPrefixRestartEndpointMass.restart_suffix_mass_subprobability
    r o₁ o₂ s (j - 1) current pref t
  change (∀ x, 0 ≤ restartSuffixMass r o₁ o₂ s (j - 1) current pref t x) ∧
    (∑ x, restartSuffixMass r o₁ o₂ s (j - 1) current pref t x) ≤ 1 ∧
    (∀ x, (classifyState x).val ≠ .transversal →
      restartSuffixMass r o₁ o₂ s (j - 1) current pref t x = 0) at hν
  by_cases htrans : (classifyState state).val = .transversal
  case neg =>
    have hzero := (SuccessfulPrefixRestartEndpointMass.restart_suffix_mass_subprobability
        r o₁ o₂ s j current pref t).2.2 state htrans
    change restartSuffixMass r o₁ o₂ s j current pref t state = 0 at hzero
    change restartSuffixMass r o₁ o₂ s j current pref t state ≤ _
    rw [hzero]
    apply Finset.sum_nonneg
    intro x _
    exact mul_nonneg (hν.1 x) (PositiveTimeTraceKernel.Subkernel.nonneg _ x state)
  change restartSuffixMass r o₁ o₂ s j current pref t state ≤ _
  let m := CountingMatroid.Model.Run.blockLength n r p
  let q := s.ρ ^ j
  have hq : 0 < q := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let P := IdealExchangeChain.idealChain r o₁ o₂ q (current.tables j) hn hq htable
  let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
  let K := PositiveTimeTraceKernel.iterate
    (PositiveTimeTraceKernel.returnWithin P A s.restartCap) s.τ
  let f := fun tape : ℕ → Bool =>
    restart_phase_cursor r o₁ o₂ tape s current.tables (j-1) current.bitCursor
  let E := fun tape (middle : RestartCursor n) => ∃ out : RestartCursor n,
    out.bitCursor ≤ pref.length+t ∧
    (restart_stage r o₁ o₂ tape s current.tables (j-1) (some middle)).val = some out ∧
    out.state = state
  obtain ⟨bits, original, hbits, _, horiginal, _, hpref, hprefLength⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor n r o₁ o₂ p j hj pref hprefix
  have hp : pref <+: bits := hpref ▸ List.take_prefix _ _
  have hconcat : pref ++ bits.drop pref.length = bits := (List.prefix_append_drop hp).symm
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
  have htotal : pref.length+t = m := Nat.add_sub_of_le hlen
  have hf : ChainStepIntervalReplay.SuccessReplay f RestartCursor.bitCursor pref.length := by
    intro tape out hr
    have hi := restart_phase_cursor_success_interval r o₁ o₂ s current.tables
      (j-1) current.bitCursor tape out hr
    exact ⟨hstart.trans hi.1, fun other hagree =>
      hi.2 other (fun i hlo hhi => hagree i (hstart.trans hlo) hhi)⟩
  have htransStart : ∀ tape middle, f tape = some middle →
      (classifyState middle.state).val = .transversal := by
    intro tape middle hr
    have hp := restart_phase_cursor_projection r o₁ o₂ tape s current.tables (j-1)
      current.bitCursor
    dsimp only [f] at hr
    rw [hr] at hp
    exact RestartPhaseTransversal.restartPhase_transversal r o₁ o₂ tape s current.tables
      (j-1) current.bitCursor (middle.state,middle.bitCursor) hp
  have hstep : ∀ (head : List Bool) (u : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      FiniteStoppedFiberMass.fairMass head u (fun tape => ∃ stop, stop ≤ head.length+u ∧
        (chainStep r o₁ o₂ tape s.drawTrials q (current.tables j) x head.length).val =
          some (y,stop)) ≤ P x y := by
    intro head u x y hv
    have hb := CoveredChainStepSubkernel.covered_chain_step_subkernel r o₁ o₂ s.drawTrials q
      (current.tables j) hn hq htable head u x y
      (RecordedTraceContinuationBound.classified_card x hv) hv
    convert hb using 1
    unfold FiniteStoppedFiberMass.fairMass CoveredChainStepSubkernel.coveredChainStepMass
    apply Finset.sum_congr rfl
    intro suffix _
    unfold FiniteStoppedFiberMass.finiteTape
    split_ifs <;> rfl
  have hleft : restartSuffixMass r o₁ o₂ s j current pref t state ≤
      FiniteStoppedFiberMass.fairMass pref t (fun tape => ∃ middle,
        f tape = some middle ∧ E tape middle) := by
    rw [restart_suffix_mass_final_stage r o₁ o₂ s j hjpos current pref t state]
    unfold FiniteStoppedFiberMass.fairMass
    apply Finset.sum_le_sum
    intro suffix _
    by_cases hs : ((restart_stage r o₁ o₂
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables (j-1)
        (f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)))).val).map
          RestartCursor.state = some state
    · obtain ⟨middle, out, hm, hout, hstate, _⟩ :=
        (restart_final_stage_event_iff r o₁ o₂ _ s current.tables (j-1)
          (f _) state).mp hs
      dsimp only [f] at hm
      have hfullrun : restart_phase_cursor r o₁ o₂
          (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables j
          current.bitCursor = some out := by
        have hsplit := restart_phase_cursor_succ r o₁ o₂
          (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables (j-1)
          current.bitCursor
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos), hm, hout] at hsplit
        exact hsplit
      have hr : (restartPhase r o₁ o₂
          (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) s current.tables j
          current.bitCursor).val = some (out.state,out.bitCursor) := by
        rw [restart_phase_cursor_projection, hfullrun]
        rfl
      have hc := RestartPhaseBitCoverage.restart_phase_cursor_le_block n r o₁ o₂ p hn
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) j hj current
        (out.state,out.bitCursor) (hfixed suffix) hr
      have hevent : ∃ middle, f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) =
          some middle ∧ E (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)) middle :=
        ⟨middle, hm, out, by simpa only [htotal] using hc, hout, hstate⟩
      unfold FiniteStoppedFiberMass.finiteTape at hs hevent ⊢
      dsimp only [f] at hs hevent ⊢
      simp +instances only [hs, hevent, if_true, le_refl]
    · unfold FiniteStoppedFiberMass.finiteTape at hs ⊢
      dsimp only [f] at hs ⊢
      simp +instances only [hs, if_false]
      split_ifs <;> positivity
  have hbound := FiniteStoppedKernelBind.stopped_kernel_bind_bound pref t f
    RestartCursor.bitCursor hf E (fun middle => K.entry middle.state state)
    (fun middle => K.nonneg middle.state state) (by
      intro suffix middle _ hE
      obtain ⟨out, hc, hr, _⟩ := hE
      exact (restart_stage_success_interval r o₁ o₂ s current.tables (j-1) middle _ out hr).1.trans hc)
    (by
      intro middle hlo hhi head hm
      have hhead : (pref ++ head.val).length = middle.bitCursor := by
        simp only [List.length_append, head.2]
        omega
      have hbudget : (pref ++ head.val).length + (t-(middle.bitCursor-pref.length)) =
          pref.length+t := by rw [hhead]; omega
      have hv : (classifyState middle.state).val ≠ .invalid := by
        rw [htransStart _ middle hm]
        intro h
        cases h
      have hi := CappedTraceIterationSubkernel.covered_trace_fold_bound r o₁ o₂ s q
        (current.tables j) P hstep (List.range s.τ) (pref ++ head.val)
        (t-(middle.bitCursor-pref.length)) middle hhead.symm hv state
      have hmass : FiniteStoppedFiberMass.fairMass (pref ++ head.val)
          (t-(middle.bitCursor-pref.length)) (fun tape => E tape middle) =
          FiniteStoppedFiberMass.fairMass (pref ++ head.val)
          (t-(middle.bitCursor-pref.length)) (fun tape => ∃ out : RestartCursor n,
            out.bitCursor ≤ (pref ++ head.val).length + (t-(middle.bitCursor-pref.length)) ∧
            CappedTraceIterationSubkernel.traceFold r o₁ o₂ tape s q (current.tables j)
              (List.range s.τ) (some middle) = some out ∧ out.state = state) := by
        unfold FiniteStoppedFiberMass.fairMass
        apply Finset.sum_congr rfl
        intro tail _
        simp only [E, q, hbudget, restart_stage_eq_trace_fold,
          Nat.sub_add_cancel (Nat.succ_le_of_lt hjpos)]
      rw [hmass]
      simpa only [List.length_range] using hi)
  have hright : (∑ suffix : List.Vector Bool t, (1 / (2 : ℝ)^t) *
      ((f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val))).map
        (fun middle => K.entry middle.state state)).getD 0) =
      ∑ x, restartSuffixMass r o₁ o₂ s (j-1) current pref t x * K.entry x state := by
    unfold restartSuffixMass
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro suffix _
    simp only [restart_phase_cursor_projection, Option.map_map]
    change (1 / (2 : ℝ)^t) *
      ((f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val))).map
        (fun middle => K.entry middle.state state)).getD 0 =
      ∑ x : PairedSet n,
        (if (f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val))).map
          RestartCursor.state = some x then 1 / (2 : ℝ)^t else 0) * K.entry x state
    have hterm (outcome : Option (RestartCursor n)) : (1 / (2 : ℝ)^t) *
        (outcome.map (fun middle => K.entry middle.state state)).getD 0 =
        ∑ x : PairedSet n,
          (if outcome.map RestartCursor.state = some x then 1 / (2 : ℝ)^t else 0) *
            K.entry x state := by
      cases outcome with
      | none => simp only [Option.map_none, Option.getD_none, mul_zero, reduceCtorEq,
          if_false, zero_mul, Finset.sum_const_zero]
      | some middle => simp only [Option.map_some, Option.getD_some, Option.some.injEq,
          ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    exact hterm (f (FiniteStoppedFiberMass.finiteTape (pref ++ suffix.val)))
  exact hleft.trans (hbound.trans_eq hright)

end CountingMatroid.Analysis.CappedRestartFinalTraceDomination

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · dependency-blocked · final recheck cannot load CountingMatroid.Analysis.CoveredChainStepSubkernel because its object is unavailable after the concurrent dependency build failed; the target and every new helper had already passed standalone elaboration. No local proof obligation remains open, and the active dependency source was not edited.

* 2026-10-09 · verified · standalone elaboration closes the target with no local proof gaps; all four support modules built. Parent publication encountered concurrent CoveredChainStepSubkernel compiler errors at lines 142–147, so no edits were made to that dependency.

* 2026-10-09 · proved · closed capped_restart_final_trace_domination through proved stopped-result disintegration, globally capped return-scan recursion, covered trace iteration, and restart-only block coverage; preserved the statement, old imports, and preceding proof progress.

* 2026-10-09 · exposed · last-stage finite-suffix domination uses the concrete positive-time return kernel; direct one-step application has the wrong event and cursor index. The independent stopping-prefix composition is ready for the live OPEN handoff.
-/
