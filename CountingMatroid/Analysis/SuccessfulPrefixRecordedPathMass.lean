import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.SuccessfulPrefixRecordedTraceSubkernel
import CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

set_option autoImplicit false

/-!
The law boundary for warm observation trajectories: the finite Boolean suffix
law is pushed forward to the list of states actually recorded by observePhase.
Abort executions have no path. The comparison law projects the ideal stationary
path onto its first N vertices, summing out the final unused transition.
The operational projection and accumulator identities are proved. Pointwise
mass domination reduces to the independent capped observation subkernel and
warm restart endpoint comparisons; both are explicit child obligations.
-/
namespace CountingMatroid.Analysis.SuccessfulPrefixRecordedPathMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE
open CountingMatroid.Analysis.RecordedObservationTrajectory

/-- INTERNAL: Record the observation trajectory from a fixed reached cursor,
using the original capped restart, draws, and tape.
TEXLINE: main.tex:1207-1212,1392-1421 -/
noncomputable def fixedObservationTrace {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (j : ℕ) (current : AnnealingCursor n) :
    Option (ObservationCursor n × List (PairedSet n)) := do
  let start ← (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val
  observePhaseTrace r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start

/-- INTERNAL: Forgetting recorded states recovers the original phase data
when history reaches the fixed cursor. -/
theorem fixed_trace_data {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current) :
    (fixedObservationTrace r o₁ o₂ tape s j current).map (fun result => (current, result.1)) =
      phaseObservationData r o₁ o₂ tape s j := by
  simp only [fixedObservationTrace, phaseObservationData, hhistory,
    Option.bind_eq_bind, Option.bind_some]
  cases hs : (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val with
  | none => simp only [Option.bind_none, Option.map_none]
  | some start =>
    simp only [Option.bind_some]
    rw [← recorded_trace_observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start]
    cases observePhaseTrace r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start <;> rfl

/-- INTERNAL: Each successful fixed-cursor trace has the required length
and reproduces all the empirical averages. -/
theorem fixed_trace_values {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (observed : ObservationCursor n) (states : List (PairedSet n))
    (htrace : fixedObservationTrace r o₁ o₂ tape s j current = some (observed, states)) :
    states.length = s.observations ∧ ∀ index : Observable n,
      (empiricalMean s observed index : ℝ) =
        (states.map (operationalObservable r o₁ o₂ s.ρ index)).sum / (s.observations : ℝ) := by
  unfold fixedObservationTrace at htrace
  cases hs : (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val with
  | none => simp only [hs, Option.bind_eq_bind, Option.bind_none, reduceCtorEq] at htrace
  | some start =>
    simp only [hs, Option.bind_eq_bind, Option.bind_some] at htrace
    have hobs : (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val =
        some observed := by
      rw [← recorded_trace_observePhase, htrace]
      rfl
    obtain ⟨states', htrace', hlength, hmean⟩ := recorded_trace_of_observation
      r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start observed hobs
    have heq : states' = states :=
      congrArg Prod.snd (Option.some.inj (htrace'.symm.trans htrace))
    subst states'
    exact ⟨hlength, hmean⟩

/-- INTERNAL: The realized finite path on successful executions; aborts map
to none. The length check only packages the proved trace-length invariant. -/
noncomputable def realizedObservationPath {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (j : ℕ) (current : AnnealingCursor n) : Option (List.Vector (PairedSet n) s.observations) :=
  match fixedObservationTrace r o₁ o₂ tape s j current with
  | none => none
  | some (_, states) => if h : states.length = s.observations then some ⟨states, h⟩ else none

/-- INTERNAL: The realized-path packaging preserves the original completed
squared error and makes its path-average meaning explicit.
TEXLINE: main.tex:1181-1187,1241-1255 -/
theorem realized_path_error {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current)
    (hN : 0 < s.observations) (index : Observable n) :
    (observationSquaredError r o₁ o₂ tape s j index : ℝ) =
      match realizedObservationPath r o₁ o₂ tape s j current with
      | none => 0
      | some states =>
          ((states.val.map (operationalObservable r o₁ o₂ s.ρ index)).sum /
            (s.observations : ℝ) - (observableMean r o₁ o₂ s j current index : ℝ)) ^ 2 := by
  classical
  have hdata := fixed_trace_data r o₁ o₂ tape s j current hhistory
  cases ht : fixedObservationTrace r o₁ o₂ tape s j current with
  | none =>
    simp only [ht, Option.map_none] at hdata
    simp only [realizedObservationPath, ht, observationSquaredError, ← hdata, Rat.cast_zero]
  | some pair =>
    rcases pair with ⟨observed, states⟩
    simp only [ht, Option.map_some] at hdata
    obtain ⟨hlength, hmean⟩ := fixed_trace_values r o₁ o₂ tape s j current observed states ht
    simp only [realizedObservationPath, ht, dif_pos hlength,
      observationSquaredError, ← hdata, if_pos (And.intro hgood hN),
      Rat.cast_pow, Rat.cast_sub, hmean index]

/-- INTERNAL: The first N vertices of an ideal path with N transitions. -/
def stationaryPathProjection {Ω : Type} (N : ℕ) (path : Fin (N + 1) → Ω) :
    List.Vector Ω N :=
  ⟨List.ofFn (fun i : Fin N => path i.castSucc), by simp⟩

/-- INTERNAL: The stationary ideal law of the recorded N vertices, summing
out the last unused transition.
TEXLINE: main.tex:982-1013,1241-1255 -/
noncomputable def stationaryRecordedMass {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (π : Arlib.Probability.FinDist Ω) (P : Arlib.MarkovChains.FinChain Ω)
    (N : ℕ) (states : List.Vector Ω N) : ℝ :=
  ∑ path : Fin (N + 1) → Ω,
    if stationaryPathProjection N path = states then
      π (path 0) * ∏ i : Fin N, P (path i.castSucc) (path i.succ) else 0

/-- INTERNAL: Projected stationary path masses are nonnegative. -/
theorem stationary_recorded_mass_nonneg {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (π : Arlib.Probability.FinDist Ω) (P : Arlib.MarkovChains.FinChain Ω)
    (N : ℕ) (states : List.Vector Ω N) :
    0 ≤ stationaryRecordedMass π P N states := by
  unfold stationaryRecordedMass
  apply Finset.sum_nonneg
  intro path _
  split_ifs
  · exact mul_nonneg (π.coe_nonneg _) (Finset.prod_nonneg (fun i _ => P.coe_nonneg _ _))
  · exact le_rfl

/-- INTERNAL: Projection preserves the exact stationary squared-average
moment, rather than replacing the correlated observations by independent ones.
TEXLINE: main.tex:982-1013,1241-1255 -/
theorem stationary_recorded_mass_moment {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (π : Arlib.Probability.FinDist Ω) (P : Arlib.MarkovChains.FinChain Ω)
    (G : Ω → ℝ) (N : ℕ) :
    (∑ states : List.Vector Ω N, stationaryRecordedMass π P N states *
      ((states.val.map G).sum / (N : ℝ) - Arlib.Probability.FinDist.Ex π G) ^ 2) =
        trajectorySquaredMoment π P G N := by
  classical
  unfold stationaryRecordedMass trajectorySquaredMoment
  simp_rw [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro path _
  simp only [ite_mul, zero_mul]
  rw [Finset.sum_eq_single (stationaryPathProjection N path)]
  · rw [if_pos rfl]
    simp only [stationaryPathProjection, List.map_ofFn, List.sum_ofFn, Function.comp_apply]
  · intro states _ hne
    exact if_neg (Ne.symm hne)
  · intro hmissing
    exact False.elim (hmissing (Finset.mem_univ _))

/-- INTERNAL: Push the finite suffix law through the actual capped restart
and recorded observation path. Aborted suffixes contribute zero mass.
TEXLINE: main.tex:1207-1212,1392-1421 -/
noncomputable def recordedSuffixMass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (states : List.Vector (PairedSet n) s.observations) : ℝ := by
  classical
  exact ∑ suffix : List.Vector Bool t,
    if realizedObservationPath r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current = some states
    then 1 / (2 : ℝ) ^ t else 0

/-- INTERNAL: Pointwise warm domination of actual recorded-path masses.
This is the law comparison underlying the successful-prefix moment bound;
its fixed cursor is obtained by deterministic history replay, not assumed to
be a newly randomized starting state.
TEXLINE: main.tex:1020-1087,1207-1240,1392-1421 -/
theorem successful_prefix_recorded_path_mass_domination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
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
    recordedSuffixMass r o₁ o₂ s j current pref t states ≤
      (10 * (n : ℝ) ^ 2) * stationaryRecordedMass
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j) current.currentWeights hq hw)
        (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j) current.currentWeights hn hq hw)
        s.observations states := by
  classical
  dsimp only
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
    current.currentWeights hn hq hw
  have hmass : recordedSuffixMass r o₁ o₂ s j current pref t states =
      SuccessfulPrefixRecordedTraceSubkernel.cappedRecordedTraceMass
        r o₁ o₂ s j current pref t states := by
    unfold recordedSuffixMass SuccessfulPrefixRecordedTraceSubkernel.cappedRecordedTraceMass
    apply Finset.sum_congr rfl
    intro suffix _
    change (if realizedObservationPath r o₁ o₂ _ s j current = some states then _ else _) =
      (if ∃ observed, fixedObservationTrace r o₁ o₂ _ s j current =
        some (observed, states.val) then _ else _)
    cases ht : fixedObservationTrace r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false) s j current with
    | none => simp [realizedObservationPath, ht]
    | some result =>
      rcases result with ⟨observed, recorded⟩
      have hlength := (fixed_trace_values r o₁ o₂ _ s j current observed recorded ht).1
      simp [realizedObservationPath, ht, hlength]
      congr 1
      apply propext
      constructor
      · intro heq
        exact congrArg Subtype.val (Option.some.inj heq)
      · intro heq
        exact congrArg some (Subtype.ext heq)
  calc
    _ = SuccessfulPrefixRecordedTraceSubkernel.cappedRecordedTraceMass
        r o₁ o₂ s j current pref t states := hmass
    _ ≤ SuccessfulPrefixRecordedTraceSubkernel.restartRecordedMass
        r o₁ o₂ s j current pref t P states :=
      SuccessfulPrefixRecordedTraceSubkernel.successful_prefix_recorded_trace_subkernel
        n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix
        current hw hfixed states
    _ ≤ (10 * (n : ℝ) ^ 2) * stationaryRecordedMass
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hq hw) P s.observations states := by
      unfold SuccessfulPrefixRecordedTraceSubkernel.restartRecordedMass stationaryRecordedMass
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro path _
      have hproj : stationaryPathProjection s.observations path = states ↔
          List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val :=
        Subtype.ext_iff
      by_cases heq : List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val
      · rw [if_pos heq, if_pos (hproj.mpr heq)]
        have hwarm :=
          SuccessfulPrefixRestartEndpointMass.successful_prefix_restart_endpoint_mass_domination
            n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix
            current hw hgood hfixed (path 0)
        exact (mul_le_mul_of_nonneg_right hwarm
          (Finset.prod_nonneg (fun i _ => P.coe_nonneg _ _))).trans_eq (mul_assoc _ _ _)
      · rw [if_neg heq, if_neg (fun h => heq (hproj.mp h)), mul_zero]

end CountingMatroid.Analysis.SuccessfulPrefixRecordedPathMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · retained · live handoff recorded-path-domination-20261008-wave1 was mechanically rejected without diagnostic; retain both support files. The parent assembly elaborates, but both operational child comparisons remain open, so the theorem is not proved outright.

* 2026-10-08 · decomposed · proved the parent finite-sum assembly and exact trace/vector event identity using two independent operational child comparisons. Both children elaborate and are Lake-published; their warm endpoint and adaptive successful-path laws remain open for live handoff.

* 2026-10-08 · retained · live handoff recorded-path-mass-20261008-a2 was mechanically rejected; retain this file. Source-only elaboration checks every statement and all helper proofs; only successful_prefix_recorded_path_mass_domination has an open proof. The requested Lake publication did not receive a grant.

* 2026-10-08 · reduced · constructed the fixed-cursor realized path and exact error identity, proved the projected ideal moment identity, and stated pointwise capped-path domination. Unreachable paths close by zero mass; unfolding a reachable path exposes the still-missing finite-block capped-draw subkernel and warm trace endpoint comparisons.
-/
