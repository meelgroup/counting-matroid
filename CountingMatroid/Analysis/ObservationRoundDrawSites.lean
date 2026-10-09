import CountingMatroid.Analysis.PhaseResourcePrimitives
import CountingMatroid.Analysis.RestartPhaseTransversal
import CountingMatroid.Analysis.ChainStepNoninvalid
import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.ObservePhaseIntervalReplay
import CountingMatroid.Analysis.RestartPhaseIntervalReplay
import CountingMatroid.Analysis.SinglePhaseIntervalReplay
import CountingMatroid.Analysis.SuccessfulPhaseReplay
import CountingMatroid.Analysis.ChainDrawSiteReplay
import CountingMatroid.Analysis.ChainDrawAbortAttribution

set_option autoImplicit false

/-!
The three stopped draw descriptors of one actual observation attempt. Each
descriptor records an absolute bit cursor and the actual draw denominator.
History, restart, and observation replay compose with the chain-level
stopped-draw replay and abort-attribution invariants. The independent
selector correctness proof is isolated in a child module; trial coverage remains
a separate quantitative obligation.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawCover
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: One reached failing round of the actual observation loop,
retaining the successful phase history, restart, and shorter observation
prefix on the same defaulted finite tape. Changing only `observations`
truncates the loop and leaves every transition parameter unchanged.
TEXLINE: main.tex:1177-1187,1392-1421 -/
def ReachedObservationRoundAbort (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (pref : List Bool) (k : ℕ)
    (suffix : List Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let tape := fun i => ((pref ++ suffix)[i]?).getD false
  (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s a) ∧
  ∃ current : AnnealingCursor n,
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
    ∃ start,
      (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val =
        some start ∧
      ∃ reached : ObservationCursor n,
        (observePhase r o₁ o₂ tape {s with observations := k}
          (s.ρ ^ j) current.currentWeights start).val = some reached ∧
        (observePhase r o₁ o₂ tape {s with observations := k + 1}
          (s.ρ ^ j) current.currentWeights start).val = none

end CountingMatroid.Analysis.ObservationRoundDrawCover

namespace CountingMatroid.Analysis.ObservationRoundDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawCover

/-- INTERNAL: Compose the stopped draw with the actual successful phase
history, restart, and k-observation prefix, all on the given finite tape.
TEXLINE: main.tex:1177-1187,1392-1421 -/
noncomputable def observationDrawSite (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (pref : List Bool) (k : ℕ) (site : Fin 3) (suffix : List Bool) :
    Option (ℕ × ℕ) := do
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let tape := fun i => ((pref ++ suffix)[i]?).getD false
  let current ← BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j
  let start ← (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val
  let reached ← (observePhase r o₁ o₂ tape {s with observations := k}
    (s.ρ ^ j) current.currentWeights start).val
  if k = 0 then none else
    chainDrawSite r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights
      reached.state reached.bitCursor site

/-- INTERNAL: Composing a stopped draw with successful history and loop
prefixes preserves its positive denominator.
TEXLINE: main.tex:1392-1421 -/
theorem observationDrawSite_positive (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (pref : List Bool) (k : ℕ) (site : Fin 3) (suffix : List Bool)
    (d : ℕ × ℕ) (hn : 0 < n)
    (h : observationDrawSite n r o₁ o₂ p j pref k site suffix = some d) :
    0 < d.2 := by
  unfold observationDrawSite at h
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
  obtain ⟨current, hh, start, hs, reached, ho, h⟩ := h
  split at h
  · cases h
  · exact chainDrawSite_positive r o₁ o₂ _ _ _ _ _ _ site d hn h

/-- INTERNAL: Recording the initial transversal cannot abort and draws
no chain bits; the observation loop with one observation therefore succeeds.
TEXLINE: main.tex:1177-1187 -/
private theorem observePhase_first_not_none {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ)
    (htransversal : (classifyState start.1).val = .transversal) :
    (observePhase r o₁ o₂ tape {s with observations := 1} q weights start).val ≠ none := by
  simp only [observePhase, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.repeatFor, List.range_one,
    Arlib.Computation.Charged.val_foldl_cons, Arlib.Computation.Charged.val_foldl_nil,
    Model.Operations.natEqual, Arlib.Computation.Charged.val_op,
    beq_self_eq_true, ite_true]
  simp only [recordObservation, Arlib.Computation.Charged.val_bind,
    htransversal, Arlib.Computation.Charged.val_pure]
  intro hfail
  cases hfail

/-- INTERNAL: A successful record certifies a non-invalid state. -/
private theorem recordObservation_success_noninvalid {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    (classifyState next.state).val ≠ .invalid := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  cases hk : (classifyState current.state).val with
  | invalid => simp only [hk, Arlib.Computation.Charged.val_pure, reduceCtorEq] at h
  | transversal =>
      simp only [hk, Arlib.Computation.Charged.val_bind] at h
      cases (Option.some.inj h).symm
      rw [hk]
      intro hbad
      cases hbad
  | defect i j =>
      simp only [hk, Arlib.Computation.Charged.val_bind] at h
      cases (Option.some.inj h).symm
      rw [hk]
      intro hbad
      cases hbad

/-- INTERNAL: The successful observation prefix retains a non-invalid state,
including a zero-length prefix of a valid restart endpoint. -/
private theorem observePhase_success_noninvalid {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (reached : ObservationCursor n)
    (hstart : (classifyState start.1).val ≠ .invalid)
    (h : (observePhase r o₁ o₂ tape s q weights start).val = some reached) :
    (classifyState reached.state).val ≠ .invalid := by
  let P : Option (ObservationCursor n) → Prop := fun outcome =>
    ∀ current, outcome = some current → (classifyState current.state).val ≠ .invalid
  let step : Option (ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
        (Option (ObservationCursor n)) := fun outcome index => do
    match outcome with
    | none => pure none
    | some current =>
        let onStart ← Model.Operations.natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ
                ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hstep : ∀ outcome index, P outcome → P (step outcome index).val := by
    intro outcome index _ next hn
    cases outcome with
    | none => cases hn
    | some current =>
        dsimp only [step] at hn
        simp only [Arlib.Computation.Charged.val_bind] at hn
        split at hn
        · exact recordObservation_success_noninvalid r o₁ o₂ s.ρ current next hn
        · simp only [Arlib.Computation.Charged.val_bind] at hn
          split at hn
          · cases hn
          · exact recordObservation_success_noninvalid r o₁ o₂ s.ρ _ next hn
  let initial : ObservationCursor n := ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩
  have hi : P (some initial) := by
    intro current hc
    cases (Option.some.inj hc).symm
    exact hstart
  have hfold := BoundedRunResourceEnvelope.chargedFold_preserves P step hstep
    (List.range s.observations) (some initial) hi
  change (Arlib.Computation.Charged.foldl step (List.range s.observations)
    (some initial)).val = some reached at h
  exact hfold reached h

/-- INTERNAL: The next noninitial observation can abort only through its
chain attempt, once the reached prefix state is non-invalid. -/
private theorem observation_next_abort_chain_none {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (k : ℕ) (reached : ObservationCursor n)
    (hk : k ≠ 0) (hvalid : (classifyState reached.state).val ≠ .invalid)
    (ho : (observePhase r o₁ o₂ tape {s with observations := k} q weights start).val = some reached)
    (hf : (observePhase r o₁ o₂ tape {s with observations := k + 1} q weights start).val = none) :
    (chainStep r o₁ o₂ tape s.drawTrials q weights reached.state reached.bitCursor).val = none := by
  let step : Option (ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
        (Option (ObservationCursor n)) := fun outcome index => do
    match outcome with
    | none => pure none
    | some current =>
        let onStart ← Model.Operations.natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ
                ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have happend (xs ys : List ℕ) (initial : Option (ObservationCursor n)) :
      (Arlib.Computation.Charged.foldl step (xs ++ ys) initial).val =
      (Arlib.Computation.Charged.foldl step ys
        (Arlib.Computation.Charged.foldl step xs initial).val).val := by
    induction xs generalizing initial with
    | nil => rfl
    | cons i xs ih =>
        simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons] using
          ih (step initial i).val
  let initial : ObservationCursor n := ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩
  change (Arlib.Computation.Charged.foldl step (List.range k) (some initial)).val = some reached at ho
  change (Arlib.Computation.Charged.foldl step (List.range (k + 1)) (some initial)).val = none at hf
  rw [List.range_succ, happend, ho, Arlib.Computation.Charged.val_foldl_cons,
    Arlib.Computation.Charged.val_foldl_nil] at hf
  dsimp only [step] at hf
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.natEqual,
    Arlib.Computation.Charged.val_op, beq_eq_false_iff_ne.mpr hk, Bool.false_eq_true,
    ite_false] at hf
  cases hc : (chainStep r o₁ o₂ tape s.drawTrials q weights reached.state reached.bitCursor).val with
  | none => rfl
  | some next =>
      cases next with
      | mk state cursor =>
          simp only [hc] at hf
          have hnext := ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ tape
            s.drawTrials q weights reached.state reached.bitCursor (state, cursor) hvalid hc
          unfold recordObservation at hf
          simp only [Arlib.Computation.Charged.val_bind] at hf
          cases hkind : (classifyState state).val <;>
            simp only [hkind, Arlib.Computation.Charged.val_bind,
              Arlib.Computation.Charged.val_pure, reduceCtorEq] at hf
          exact False.elim (hnext hkind)

/-- INTERNAL: A shared list prefix and matching truncated suffix give
agreement below the absolute stopping cursor, including defaulted bits
beyond the common finite-tape length.
TEXLINE: main.tex:1392-1421 -/
theorem appended_tape_agreement (pref suffix other : List Bool) (stop : ℕ)
    (hlen : suffix.length = other.length)
    (hp : suffix.take (stop - pref.length) <+: other) :
    ∀ i < stop, ((pref ++ suffix)[i]?).getD false =
      ((pref ++ other)[i]?).getD false := by
  intro i hi
  by_cases hpre : i < pref.length
  · rw [List.getElem?_append_left hpre, List.getElem?_append_left hpre]
  · rw [List.getElem?_append_right (by omega),
      List.getElem?_append_right (by omega)]
    by_cases hsuf : i - pref.length < suffix.length
    · have htake : i - pref.length < (suffix.take (stop - pref.length)).length := by
        simp only [List.length_take]
        omega
      have heq := List.prefix_iff_getElem?.mp hp (i - pref.length) htake
      have hget := List.getElem?_eq_getElem htake
      rw [List.getElem?_take_of_lt (by omega)] at hget
      rw [heq, hget]
    · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]

/-- INTERNAL: Actual stopped draw sites are local in their consumed prefixes,
and a reached round abort is attributable to one of those three capped draws.
Trial widths and the finite-block bound are not conclusions of this lemma.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem observation_round_draw_sites (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (k : ℕ) (hk : k < (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (∀ site suffix, suffix.length = t → ∀ d,
      observationDrawSite n r o₁ o₂ p j pref k site suffix = some d →
      ∀ other, other.length = t → suffix.take (d.1 - pref.length) <+: other →
        observationDrawSite n r o₁ o₂ p j pref k site other = some d) ∧
    (∀ suffix, suffix.length = t →
      ReachedObservationRoundAbort n r o₁ o₂ p j pref k suffix →
      ∃ site d, observationDrawSite n r o₁ o₂ p j pref k site suffix = some d ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          s.drawTrials d.2 d.1).val.1 = none) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  constructor
  · intro site suffix hlen d hsite other hother htake
    -- Replay the history using successful_history_replay_of_phase_replay
    -- and single_phase_interval_replay, then restartPhase_success_interval,
    -- observePhase_success_interval, and the preceding index draws.
    -- The map stops BEFORE this draw, so its descriptor must be stable
    -- under agreement below d.1, not below the end of its capped trials.
    unfold observationDrawSite at hsite
    simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hsite
    obtain ⟨current, hhistory, start, hrestart, reached, hobserve, hdraw⟩ := hsite
    have hhistoryReplay := SuccessfulPhaseReplay.successful_history_replay_of_phase_replay
      r o₁ o₂ s (SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s)
      (fun i => ((pref ++ suffix)[i]?).getD false) j current hhistory
      (fun i => ((pref ++ other)[i]?).getD false)
    have hrestartReplay := RestartPhaseIntervalReplay.restartPhase_success_interval
      r o₁ o₂ s current.tables j current.bitCursor
      (fun i => ((pref ++ suffix)[i]?).getD false) start hrestart
    have hobserveReplay := ObservePhaseIntervalReplay.observePhase_success_interval
      r o₁ o₂ {s with observations := k} (s.ρ ^ j) current.currentWeights start
      (fun i => ((pref ++ suffix)[i]?).getD false) reached hobserve
    split at hdraw
    · cases hdraw
    · rename_i hkzero
      have hdrawReplay := chainDrawSite_success_interval r o₁ o₂ s
        (s.ρ ^ j) current.currentWeights reached.state reached.bitCursor site
        (fun i => ((pref ++ suffix)[i]?).getD false) d hdraw
      have hagree := appended_tape_agreement pref suffix other d.1
        (hlen.trans hother.symm) htake
      have hcurr : current.bitCursor ≤ d.1 :=
        hrestartReplay.1.trans (hobserveReplay.1.trans hdrawReplay.1)
      have hh := hhistoryReplay (fun i hi => hagree i (hi.trans_le hcurr))
      have hs := hrestartReplay.2 (fun i => ((pref ++ other)[i]?).getD false)
        (fun i _ hi => hagree i
          (hi.trans_le (hobserveReplay.1.trans hdrawReplay.1)))
      have ho := hobserveReplay.2 (fun i => ((pref ++ other)[i]?).getD false)
        (fun i _ hi => hagree i (hi.trans_le hdrawReplay.1))
      have hd := hdrawReplay.2 (fun i => ((pref ++ other)[i]?).getD false)
        (fun i _ hi => hagree i hi)
      dsimp only [s] at hh hs ho hd
      unfold observationDrawSite
      simp only [Option.bind_eq_bind, hh, hs, ho, Option.bind_some,
        hkzero, ite_false]
      exact hd

  · intro suffix hlen hbad
    obtain ⟨hprevious, current, hhistory, start, hrestart, reached, hobserve, hfail⟩ := hbad
    have hrestartInterval :=
      RestartPhaseIntervalReplay.restartPhase_success_interval r o₁ o₂ s
        current.tables j current.bitCursor
        (fun i => ((pref ++ suffix)[i]?).getD false) start hrestart
    have hobserveInterval :=
      ObservePhaseIntervalReplay.observePhase_success_interval r o₁ o₂
        {s with observations := k} (s.ρ ^ j) current.currentWeights start
        (fun i => ((pref ++ suffix)[i]?).getD false) reached hobserve
    have htransversal := RestartPhaseTransversal.restartPhase_transversal
      r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false) s current.tables
      j current.bitCursor start hrestart
    by_cases hkzero : k = 0
    · rw [hkzero] at hfail
      exact False.elim ((observePhase_first_not_none r o₁ o₂ _ s (s.ρ ^ j)
        current.currentWeights start htransversal) hfail)
    · have hvalid := observePhase_success_noninvalid r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) {s with observations := k}
        (s.ρ ^ j) current.currentWeights start reached
        (by rw [htransversal]; intro hbad; cases hbad) hobserve
      have hchain := observation_next_abort_chain_none r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s (s.ρ ^ j)
        current.currentWeights start k reached hkzero hvalid hobserve hfail
      obtain ⟨site, d, hsite, hdrawfail⟩ := chain_abort_draw_site r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s (s.ρ ^ j)
        current.currentWeights reached.state reached.bitCursor hvalid hchain
      refine ⟨site, d, ?_, hdrawfail⟩
      unfold observationDrawSite
      simp only [Option.bind_eq_bind, hhistory, hrestart, hobserve,
        Option.bind_some, hkzero, ite_false]
      exact hsite

end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · proved · closed observation_round_draw_sites with proved stopped-draw replay, sampler range, classifier weight, and selector correctness helpers; preserved the statement and every original import. Both live handoffs were mechanically rejected without diagnostic, so all child proofs were completed vertically.
* r28 · narrowed · after mechanical rejection of r28-observation-draw-sites-1 without diagnostic, proved the chain replay and abort-attribution children; isolated the remaining classifier-valid selection population/count bridge in ClassifiedStateSelection.
* r28 · composed · removed the parent’s local proof gaps by composing history, restart, observation and stopped-chain replay; attributed reached aborts using the independent chain abort helper. Both child statements elaborate; their chain-level proofs are prepared for the live OPEN handoff.
* r27 · decomposed · defined the three pre-draw stopping descriptors; attempted prefix replay and abort attribution, exposing the n-element-state/selection and stopping-locality obligations separately from trial coverage.
-/
