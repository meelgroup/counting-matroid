import CountingMatroid.Analysis.SuccessfulPrefixRecordedPathMass
import CountingMatroid.Analysis.StationaryObservableMSE
import CountingMatroid.Analysis.SuccessfulPrefixAbortBound
import CountingMatroid.Analysis.SuccessfulPhaseReplay
import CountingMatroid.Analysis.SinglePhaseIntervalReplay

set_option autoImplicit false

/-!
The operational coupling needed for a successful consumed prefix: completed
finite-tape observation errors are dominated by 10 n² times the stationary
ideal trajectory moment at a single fixed good phase cursor. This does not
assert the stationary time-average estimate; that is a separate obligation.
Deterministic history replay and the fixed-mean error identity are proved,
including prefixes truncated at the end of their finite block. The expectation bound is reduced by exact finite pushforward identities to
pointwise recorded-path mass domination in SuccessfulPrefixRecordedPathMass;
that stochastic comparison remains open there.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE

/-- INTERNAL: Regroup a finite weighted execution sum by its recorded path.
This transfers expectations without identifying distinct sample spaces.
TEXLINE: main.tex:1207-1255,1415-1421 -/
theorem weighted_fiber_sum {α β : Type} [Fintype β] [DecidableEq β]
    (S : Finset α) (f : α → β) (w : α → ℝ) (g : β → ℝ) :
    (∑ x ∈ S, w x * g (f x)) =
      ∑ y : β, (∑ x ∈ S, if f x = y then w x else 0) * g y := by
  classical
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  simp only [ite_mul, zero_mul]
  simp

/-- INTERNAL: Replacing the unconsumed part of a finite tape preserves its
reached phase cursor. If the consumed cursor is beyond the block, the prefix
is the entire block and there is only the empty suffix; no coverage premise
is needed for this deterministic replay statement.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem phase_history_after_consumed_prefix {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j m : ℕ)
    (bits pref : List Bool) (current : AnnealingCursor n)
    (hlen : bits.length = m)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
      (fun i => (bits[i]?).getD false) s j = some current)
    (hpref : pref = bits.take current.bitCursor)
    (suffix : List.Vector Bool (m - pref.length)) :
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j = some current := by
  by_cases hwithin : current.bitCursor ≤ m
  · apply SuccessfulPhaseReplay.successful_history_replay_of_phase_replay
      r o₁ o₂ s (SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s)
      (fun i => (bits[i]?).getD false) j current hhistory
    intro i hi
    have hipref : i < pref.length := by
      rw [hpref, List.length_take, hlen, Nat.min_eq_left hwithin]
      exact hi
    rw [List.getElem?_append_left hipref, hpref, List.getElem?_take_of_lt hi]
  · have hprefFull : pref = bits := by
      rw [hpref, List.take_of_length_le (by omega)]
    have hsuffix : suffix.val = [] := by
      apply List.length_eq_zero_iff.mp
      rw [suffix.property, hprefFull, hlen, Nat.sub_self]
    simpa only [hprefFull, hsuffix, List.append_nil] using hhistory

/-- INTERNAL: Once history replay fixes the phase cursor, every completed
observation is centered at that cursor's stationary mean. This also retains
zero error on either operational abort, without conditioning away the abort.
TEXLINE: main.tex:1207-1212,1241-1255 -/
theorem observation_squared_error_at_cursor {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current)
    (hN : 0 < s.observations) (index : Observable n) :
    observationSquaredError r o₁ o₂ tape s j index =
      match phaseObservationData r o₁ o₂ tape s j with
      | none => 0
      | some (_, observed) =>
          (empiricalMean s observed index - observableMean r o₁ o₂ s j current index) ^ 2 := by
  classical
  cases hdata : phaseObservationData r o₁ o₂ tape s j with
  | none => simp only [observationSquaredError, hdata]
  | some pair =>
      rcases pair with ⟨reached, observed⟩
      have hreached := ((observation_data_iff r o₁ o₂ tape s j reached observed).mp hdata).1
      rw [hhistory] at hreached
      have heq : reached = current := (Option.some.inj hreached).symm
      subst reached
      simp only [observationSquaredError, hdata, if_pos (And.intro hgood hN)]

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
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hfixed (suffix : List.Vector Bool (m - pref.length)) :
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j = some current :=
    phase_history_after_consumed_prefix r o₁ o₂ s j m bits pref current
      hlen hhistory hpref suffix
  have hN : 0 < s.observations :=
    (FinitePhaseEstimationBound.schedule_estimation_budget n p hn).2.1
  have herr (suffix : List.Vector Bool (m - pref.length)) :=
    observation_squared_error_at_cursor r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current
      (hfixed suffix) hstored hN index
  let hw := good_current_weights_pos n r o₁ o₂ p hn j current hstored
  let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let π := IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
    current.currentWeights hq hw
  let G := operationalObservable r o₁ o₂ s.ρ index
  let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
    current.currentWeights hn hq hw
  have hmoment : 0 ≤ stationaryObservationMoment n r o₁ o₂ p hn j current hw index := by
    unfold stationaryObservationMoment trajectorySquaredMoment
    apply Finset.sum_nonneg
    intro path _
    exact mul_nonneg (mul_nonneg (π.coe_nonneg (path 0))
      (Finset.prod_nonneg (fun (i : Fin s.observations) _ =>
        P.coe_nonneg (path i.castSucc) (path i.succ)))) (sq_nonneg _)
  have hmean : Arlib.Probability.FinDist.Ex π G =
      (observableMean r o₁ o₂ s j current index : ℝ) :=
    operational_observable_mean n r o₁ o₂ p hn j current hw index
  have herrReal (suffix : List.Vector Bool (m - pref.length)) :
      (observationSquaredError r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) =
      match phaseObservationData r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j with
      | none => 0
      | some (_, observed) =>
          ((empiricalMean s observed index : ℝ) - Arlib.Probability.FinDist.Ex π G) ^ 2 := by
    rw [herr suffix]
    cases hdata : phaseObservationData r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j with
    | none => simp only [Rat.cast_zero]
    | some pair =>
        rcases pair with ⟨reached, observed⟩
        simp only [hmean, Rat.cast_pow, Rat.cast_sub]
  refine ⟨current, hw, hstored, ?_⟩
  let completed := Finset.univ.filter (fun suffix : List.Vector Bool (m - pref.length) =>
    ObservationCompleted r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j)
  change (∑ suffix ∈ completed, (1 / (2 : ℝ) ^ (m - pref.length)) *
    (observationSquaredError r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) ≤
      (10 * (n : ℝ) ^ 2) *
        stationaryObservationMoment n r o₁ o₂ p hn j current hw index
  by_cases habort : completed = ∅
  · rw [habort, Finset.sum_empty]
    exact mul_nonneg (by positivity) hmoment
  · let pathOf := fun suffix : List.Vector Bool (m - pref.length) =>
      SuccessfulPrefixRecordedPathMass.realizedObservationPath r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current
    let errorOf := fun states : List.Vector (PairedSet n) s.observations =>
      ((states.val.map G).sum / (s.observations : ℝ) -
        Arlib.Probability.FinDist.Ex π G) ^ 2
    have herrPath (suffix : List.Vector Bool (m - pref.length)) :
        (observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) =
        match pathOf suffix with
        | none => 0
        | some states => errorOf states := by
      have he := SuccessfulPrefixRecordedPathMass.realized_path_error r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current
        (hfixed suffix) hstored hN index
      rw [← hmean] at he
      exact he
    have hsumAll :
        (∑ suffix ∈ completed, (1 / (2 : ℝ) ^ (m - pref.length)) *
          (observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ)) =
        ∑ suffix : List.Vector Bool (m - pref.length),
          (1 / (2 : ℝ) ^ (m - pref.length)) *
            (observationSquaredError r o₁ o₂
              (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro suffix _ hnot
      have hzero : (observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index : ℝ) = 0 := by
        cases hd : phaseObservationData r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j with
        | none => simpa only [hd] using herrReal suffix
        | some pair =>
          rcases pair with ⟨reached, observed⟩
          have hh := ((observation_data_iff r o₁ o₂ _ s j reached observed).mp hd).1
          rw [hfixed suffix] at hh
          have heq : reached = current := (Option.some.inj hh).symm
          subst reached
          exact False.elim (hnot (Finset.mem_filter.mpr
            ⟨Finset.mem_univ _, current, observed, hd, hstored, hN⟩))
      rw [hzero, mul_zero]
    rw [hsumAll]
    conv_lhs =>
      arg 2
      intro suffix
      rw [herrPath suffix]
    rw [weighted_fiber_sum Finset.univ pathOf
      (fun _ => 1 / (2 : ℝ) ^ (m - pref.length))
      (fun path => match path with | none => 0 | some states => errorOf states)]
    simp only [Fintype.sum_option, mul_zero, zero_add]
    change (∑ states : List.Vector (PairedSet n) s.observations,
      SuccessfulPrefixRecordedPathMass.recordedSuffixMass
        r o₁ o₂ s j current pref (m - pref.length) states * errorOf states) ≤
        (10 * (n : ℝ) ^ 2) * trajectorySquaredMoment π P G s.observations
    rw [← SuccessfulPrefixRecordedPathMass.stationary_recorded_mass_moment π P G s.observations,
      Finset.mul_sum]
    apply Finset.sum_le_sum
    intro states _
    have hmass := SuccessfulPrefixRecordedPathMass.successful_prefix_recorded_path_mass_domination
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix
      current hw hstored hfixed states
    exact (mul_le_mul_of_nonneg_right hmass (sq_nonneg _)).trans_eq (mul_assoc _ _ _)

end CountingMatroid.Analysis.SuccessfulPrefixTrajectoryDomination

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · retained · live handoff recorded-path-mass-20261008-a2 was mechanically rejected with no compiler diagnostic. All deterministic support proofs and the parent reduction check in a source-only probe using the existing cursor-extraction contract; standalone elaboration awaits the new module artifacts, and the requested Lake build received no grant. The pointwise stochastic child remains open and owned here.

* 2026-10-08 · decomposed · constructed the actual recorded observation trajectory, proved its accumulator identity and exact finite pushforward, and reduced the parent to pointwise recorded-path mass domination. The remaining stochastic obligation is in SuccessfulPrefixRecordedPathMass, pending live handoff.

* 2026-10-08 · reduced · proved finite consumed-prefix history replay without a coverage premise and the fixed-cursor error identity; the parent uses both, centers errors at the ideal mean, and separates the all-abort case. Expanding the stationary moment exposes different index spaces (bit suffixes and ideal paths); their stochastic comparison remains the single original open obligation.

* r24 · open · extracted the reached good cursor and proved full completed-tape length; aesop left the exact moment-domination inequality, without any trajectory-law comparison in the hypotheses. The first live child handoff was mechanically rejected without further diagnostic.
-/
