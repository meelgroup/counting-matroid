import CountingMatroid.Analysis.PhaseMeanCertificate

set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseObservationExperiment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: The reached phase cursor and the actual observation output,
retaining every restart and observation abort as `none`.
TEXLINE: main.tex:1163-1187,1207-1266 -/
noncomputable def phaseObservationData {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) :
    Option (AnnealingCursor n × ObservationCursor n) := do
  let current ← BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j
  let start ← (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val
  let observed ← (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val
  pure (current, observed)

/-- INTERNAL: Reindex type observables by pairs, with diagonal pairs repeating
 the transversal indicator. The two Boolean indices are the transversal
 indicator and the annealing numerator. This keeps the empty-defect case.
TEXLINE: main.tex:1241-1263 -/
abbrev Observable (n : ℕ) := Bool ⊕ (Fin n × Fin n)

/-- INTERNAL: The stationary mean of one concrete operational observable.
TEXLINE: main.tex:1241-1255 -/
noncomputable def observableMean {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (index : Observable n) : ℚ :=
  match index with
  | .inl false => typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights .transversal
  | .inl true => numeratorMean r o₁ o₂ (s.ρ ^ j) s.ρ current.currentWeights
  | .inr (i, k) => typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights
      (if i = k then .transversal else .defect i k)

/-- INTERNAL: The empirical mean read from the actual observation counters.
TEXLINE: main.tex:1181-1187 -/
noncomputable def empiricalMean {n : ℕ} (s : AnnealingSchedule)
    (observed : ObservationCursor n) (index : Observable n) : ℚ :=
  match index with
  | .inl false => (observed.counts .transversal : ℚ) / s.observations
  | .inl true => observed.numeratorSum / s.observations
  | .inr (i, k) =>
      (observed.counts (if i = k then .transversal else .defect i k) : ℚ) / s.observations

/-- INTERNAL: Separate operational completion from relative estimation error.
This predicate includes the deterministic invariant and a nonempty sample.
TEXLINE: main.tex:1207-1266 -/
def ObservationCompleted {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  ∃ current observed, phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
    FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧ 0 < s.observations

/-- INTERNAL: Squared deviation on completed good executions, and zero on
all other executions. This is a subprobability second moment; aborts are
bounded separately, rather than assigned an artificial empirical estimate.
TEXLINE: main.tex:1253-1266 -/
noncomputable def observationSquaredError {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (index : Observable n) : ℚ := by
  classical
  exact match phaseObservationData r o₁ o₂ tape s j with
  | none => 0
  | some (current, observed) =>
      if FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧ 0 < s.observations
      then (empiricalMean s observed index - observableMean r o₁ o₂ s j current index) ^ 2
      else 0

/-- INTERNAL: Evaluate the observation experiment by its actual restart and
observation witnesses, without replacing their tape or starting state.
TEXLINE: main.tex:1163-1187 -/
theorem observation_data_iff {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (observed : ObservationCursor n) :
    phaseObservationData r o₁ o₂ tape s j = some (current, observed) ↔
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
      ∃ start, (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val =
        some start ∧ (observePhase r o₁ o₂ tape s (s.ρ ^ j)
          current.currentWeights start).val = some observed := by
  simp only [phaseObservationData, Option.bind_eq_bind, Option.bind_eq_some_iff, Option.pure_def,
    Option.some.injEq, Prod.mk.injEq]
  constructor
  · rintro ⟨current', hh, start, hs, observed', ho, hc, hob⟩
    subst current'
    subst observed'
    exact ⟨hh, start, hs, ho⟩
  · rintro ⟨hh, start, hs, ho⟩
    exact ⟨current, hh, start, hs, observed, ho, rfl, rfl⟩

/-- INTERNAL: Relative accuracy of the finite family of concrete empirical
observables is exactly the raw phase boundary, once the operational data are
retained. Diagonal pair indices repeat an existing condition.
TEXLINE: main.tex:1241-1266 -/
theorem raw_means_iff_observation_data {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    PhaseMeanCertificate.RawPhaseMeans r o₁ o₂ tape s j ↔
      ∃ current observed,
        phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
        FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
        0 < s.observations ∧ ∀ index : Observable n,
          RelativeEstimate s.η (observableMean r o₁ o₂ s j current index)
            (empiricalMean s observed index) := by
  constructor
  · rintro ⟨current, start, observed, hh, hg, hs, ho, hN, hz, hu, hd⟩
    refine ⟨current, observed, (observation_data_iff _ _ _ _ _ _ _ _).mpr
      ⟨hh, start, hs, ho⟩, hg, hN, ?_⟩
    intro index
    cases index with
    | inl b => cases b <;> assumption
    | inr pair =>
      rcases pair with ⟨i, k⟩
      by_cases hik : i = k
      · simpa only [observableMean, empiricalMean, if_pos hik] using hz
      · simpa only [observableMean, empiricalMean, if_neg hik] using hd ⟨i, k, hik⟩
  · rintro ⟨current, observed, hdata, hg, hN, hall⟩
    obtain ⟨hh, start, hs, ho⟩ := (observation_data_iff _ _ _ _ _ _ _ _).mp hdata
    refine ⟨current, start, observed, hh, hg, hs, ho, hN,
      hall (.inl false), hall (.inl true), ?_⟩
    intro index
    simpa only [observableMean, empiricalMean, if_neg index.distinct] using
      hall (.inr (index.emptyPair, index.fullPair))

/-- INTERNAL: All the subprobability squared errors are nonnegative. -/
theorem observation_squared_error_nonneg {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (index : Observable n) :
    0 ≤ observationSquaredError r o₁ o₂ tape s j index := by
  classical
  unfold observationSquaredError
  split
  · exact le_rfl
  · split
    · exact sq_nonneg _
    · exact le_rfl

/-- INTERNAL: A consumed prefix of an actual finite run whose earlier
phase certificates all hold. Cursor coverage is deliberately an obligation
of the quantitative phase estimates, not a premise imposed on callers.
TEXLINE: main.tex:1207-1212,1392-1421 -/
def SuccessfulPhasePrefix (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (pref : List Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  ∃ bits : List Bool, bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    pref = bits.take (match BoundedRunPhaseHistory.phaseHistory r o₁ o₂
      (fun i => (bits[i]?).getD false) s j with
      | none => 0
      | some current => current.bitCursor)

end CountingMatroid.Analysis.PhaseObservationExperiment
