import CountingMatroid.Analysis.StationaryObservableMSE

set_option autoImplicit false

/-!
Record the actual states visited by the operational observation loop. The trace
retains its rejection-draw aborts and uses the supplied tape and cursors. Its
observable sums agree exactly with the program's counters and numerator sum.
This deterministic construction supplies the sample space for a subsequent
comparison with the ideal path law; it does not assert that law comparison.
-/
namespace CountingMatroid.Analysis.RecordedObservationTrajectory

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryObservableMSE

/-- INTERNAL: Read the accumulated, unnormalised operational observable. -/
noncomputable def observationTotal {n : ℕ} (current : ObservationCursor n)
    (index : Observable n) : ℝ :=
  match index with
  | .inl false => current.counts .transversal
  | .inl true => current.numeratorSum
  | .inr (i, k) => current.counts (if i = k then .transversal else .defect i k)

/-- INTERNAL: A successful record keeps the state and adds exactly its real
observable value to every accumulator.
TEXLINE: main.tex:1181-1187 -/
theorem record_observation_total {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ ρ current).val = some next)
    (index : Observable n) :
    next.state = current.state ∧
      observationTotal next index = observationTotal current index +
        operationalObservable r o₁ o₂ ρ index current.state := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  cases hk : (classifyState current.state).val with
  | invalid => simp [hk] at h
  | defect a b =>
    simp only [hk, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure] at h
    cases (Option.some.inj h).symm
    refine ⟨rfl, ?_⟩
    cases index with
    | inl flag => cases flag <;>
        simp [observationTotal, operationalObservable,
          IdealExchangeChain.typeIndicator, IdealExchangeChain.numeratorObservable,
          countIncrement, hk]
    | inr pair =>
        rcases pair with ⟨i, k⟩
        simp only [observationTotal, operationalObservable,
          IdealExchangeChain.typeIndicator, countIncrement,
          Arlib.Computation.Charged.val_opMany, hk]
        split_ifs <;> try simp only [Nat.cast_add, Nat.cast_one, add_zero]
        all_goals aesop
  | transversal =>
    simp only [hk, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure] at h
    cases (Option.some.inj h).symm
    refine ⟨rfl, ?_⟩
    cases index with
    | inl flag => cases flag <;>
        simp [observationTotal, operationalObservable,
          IdealExchangeChain.typeIndicator, IdealExchangeChain.numeratorObservable,
          countIncrement, hk, ratAdd, natSub,
          BoundedRunResourceEnvelope.ratPower_value]
    | inr pair =>
        rcases pair with ⟨i, k⟩
        simp only [observationTotal, operationalObservable,
          IdealExchangeChain.typeIndicator, countIncrement,
          Arlib.Computation.Charged.val_opMany, hk]
        split_ifs <;> try simp only [Nat.cast_add, Nat.cast_one, add_zero]

/-- INTERNAL: The charged body of one iteration of observePhase, kept with
its actual first-observation branch and capped draw failures. -/
def observationAttempt {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (index : ℕ) (current : Option (ObservationCursor n)) :
    Arlib.Computation.Charged Op Cell (Option (ObservationCursor n)) := do
  match current with
  | none => pure none
  | some current =>
      let onStart ← natEqual index 0
      if onStart then recordObservation r o₁ o₂ s.ρ current
      else
        let next ← chainStep r o₁ o₂ tape s.drawTrials q weights
          current.state current.bitCursor
        match next with
        | none => pure none
        | some (state, bitCursor) =>
            recordObservation r o₁ o₂ s.ρ
              ⟨state, bitCursor, current.counts, current.numeratorSum⟩

/-- INTERNAL: Successfully recording an iteration adds the observable of
exactly the state returned by that iteration.
TEXLINE: main.tex:1181-1187 -/
theorem observation_attempt_total {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (k : ℕ) (current next : ObservationCursor n)
    (h : (observationAttempt r o₁ o₂ tape s q weights k (some current)).val = some next)
    (index : Observable n) :
    observationTotal next index = observationTotal current index +
      operationalObservable r o₁ o₂ s.ρ index next.state := by
  unfold observationAttempt at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  by_cases hon : (natEqual k 0).val = true
  · rw [if_pos hon] at h
    obtain ⟨hstate, htotal⟩ := record_observation_total r o₁ o₂ s.ρ current next h index
    simpa only [hstate] using htotal
  · rw [if_neg hon] at h
    simp only [Arlib.Computation.Charged.val_bind] at h
    cases hc : (chainStep r o₁ o₂ tape s.drawTrials q weights
      current.state current.bitCursor).val with
    | none => simp [hc] at h
    | some step =>
      simp only [hc] at h
      obtain ⟨hstate, htotal⟩ := record_observation_total r o₁ o₂ s.ρ
        ⟨step.1, step.2, current.counts, current.numeratorSum⟩ next h index
      simpa only [hstate, observationTotal] using htotal

/-- INTERNAL: Augment the actual observation iterations with the ordered
list of recorded states. A failed draw or invalid record gives none.
TEXLINE: main.tex:1181-1187,1392-1421 -/
noncomputable def recordedObservationTrace {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n) :
    List ℕ → Option (ObservationCursor n) →
      Option (ObservationCursor n × List (PairedSet n))
  | [], current => current.map (fun c => (c, []))
  | k :: ks, current => do
      let next ← (observationAttempt r o₁ o₂ tape s q weights k current).val
      let result ← recordedObservationTrace r o₁ o₂ tape s q weights ks (some next)
      pure (result.1, next.state :: result.2)

/-- INTERNAL: Observation aborts remain absorbing in the recorded trace. -/
theorem recorded_trace_none {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (indices : List ℕ) :
    recordedObservationTrace r o₁ o₂ tape s q weights indices none = none := by
  cases indices <;> rfl

/-- INTERNAL: Erasing the extra state list recovers exactly the operational
charged observation fold, with the same input tape and all abort branches.
TEXLINE: main.tex:1181-1187 -/
theorem recorded_trace_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (indices : List ℕ) (current : Option (ObservationCursor n)) :
    (recordedObservationTrace r o₁ o₂ tape s q weights indices current).map Prod.fst =
      (Arlib.Computation.Charged.foldl
        (fun acc k => observationAttempt r o₁ o₂ tape s q weights k acc)
        indices current).val := by
  induction indices generalizing current with
  | nil => cases current <;> rfl
  | cons k ks ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons, ← ih]
    cases hc : (observationAttempt r o₁ o₂ tape s q weights k current).val with
    | none => simp only [recordedObservationTrace, Option.bind_eq_bind, hc, Option.bind_none,
        recorded_trace_none, Option.map_none]
    | some next =>
      cases ht : recordedObservationTrace r o₁ o₂ tape s q weights ks (some next) <;>
        simp only [recordedObservationTrace, Option.bind_eq_bind, hc, ht, Option.bind_some,
          Option.bind_none, Option.pure_def, Option.map_none, Option.map_some]

/-- INTERNAL: The recorded list has one state per iteration and its sum is
exactly the increment of every operational observation accumulator.
TEXLINE: main.tex:1181-1187 -/
theorem recorded_trace_totals {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (indices : List ℕ) (current final : ObservationCursor n) (states : List (PairedSet n))
    (h : recordedObservationTrace r o₁ o₂ tape s q weights indices (some current) =
      some (final, states)) (index : Observable n) :
    states.length = indices.length ∧ observationTotal final index =
      observationTotal current index +
        (states.map (operationalObservable r o₁ o₂ s.ρ index)).sum := by
  induction indices generalizing current final states with
  | nil =>
    simp only [recordedObservationTrace, Option.map_some, Option.some.injEq,
      Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp only [List.length_nil, List.map_nil, List.sum_nil, add_zero, and_self]
  | cons k ks ih =>
    cases hc : (observationAttempt r o₁ o₂ tape s q weights k (some current)).val with
    | none => simp only [recordedObservationTrace, Option.bind_eq_bind,
        hc, Option.bind_none, reduceCtorEq] at h
    | some next =>
      cases ht : recordedObservationTrace r o₁ o₂ tape s q weights ks (some next) with
      | none => simp only [recordedObservationTrace, Option.bind_eq_bind,
          hc, ht, Option.bind_some, Option.bind_none, reduceCtorEq] at h
      | some result =>
        rcases result with ⟨finished, tail⟩
        simp only [recordedObservationTrace, Option.bind_eq_bind, hc, ht,
          Option.bind_some, Option.pure_def, Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hlength, htotal⟩ := ih next finished tail ht
        refine ⟨by simp only [List.length_cons, hlength], ?_⟩
        rw [htotal, observation_attempt_total r o₁ o₂ tape s q weights k current next hc index]
        simp only [List.map_cons, List.sum_cons]
        exact add_assoc _ _ _

/-- INTERNAL: Recorded operational observations from the actual restart
endpoint, with zero initial counters and the given finite or infinite tape. -/
noncomputable def observePhaseTrace {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (start : PairedSet n × ℕ) :
    Option (ObservationCursor n × List (PairedSet n)) :=
  recordedObservationTrace r o₁ o₂ tape s q weights (List.range s.observations)
    (some ⟨start.1, start.2, (allocateCounts n).val, 0⟩)

/-- INTERNAL: Projecting the recorded full phase gives the original
observePhase output, including its abort value.
TEXLINE: main.tex:1181-1187 -/
theorem recorded_trace_observePhase {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (start : PairedSet n × ℕ) :
    (observePhaseTrace r o₁ o₂ tape s q weights start).map Prod.fst =
      (observePhase r o₁ o₂ tape s q weights start).val := by
  exact recorded_trace_projection r o₁ o₂ tape s q weights
    (List.range s.observations) _

/-- INTERNAL: Every successful observation has a concrete recorded state
list of the correct length, whose average is every empirical mean.
TEXLINE: main.tex:1181-1187,1241-1255 -/
theorem recorded_trace_of_observation {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (start : PairedSet n × ℕ)
    (observed : ObservationCursor n)
    (h : (observePhase r o₁ o₂ tape s q weights start).val = some observed) :
    ∃ states : List (PairedSet n),
      observePhaseTrace r o₁ o₂ tape s q weights start = some (observed, states) ∧
      states.length = s.observations ∧ ∀ index : Observable n,
        (empiricalMean s observed index : ℝ) =
          (states.map (operationalObservable r o₁ o₂ s.ρ index)).sum /
            (s.observations : ℝ) := by
  have hp := recorded_trace_observePhase r o₁ o₂ tape s q weights start
  rw [h] at hp
  obtain ⟨result, htrace, heq⟩ := Option.map_eq_some_iff.mp hp
  rcases result with ⟨final, states⟩
  change final = observed at heq
  subst final
  have htotals := recorded_trace_totals r o₁ o₂ tape s q weights
    (List.range s.observations)
    ⟨start.1, start.2, (allocateCounts n).val, 0⟩ observed states htrace
  refine ⟨states, htrace, ?_, ?_⟩
  · simpa only [List.length_range] using (htotals (.inl false)).1
  · intro index
    have htotal := (htotals index).2
    have hzero : observationTotal
        ⟨start.1, start.2, (allocateCounts n).val, 0⟩ index = 0 := by
      cases index with
      | inl flag => cases flag <;> simp [observationTotal, allocateCounts]
      | inr pair => simp [observationTotal, allocateCounts]
    rw [hzero, zero_add] at htotal
    have hmean : (empiricalMean s observed index : ℝ) =
        observationTotal observed index / (s.observations : ℝ) := by
      cases index with
      | inl flag => cases flag <;>
          simp only [empiricalMean, observationTotal, Rat.cast_div, Rat.cast_natCast]
      | inr pair =>
          simp only [empiricalMean, observationTotal, Rat.cast_div, Rat.cast_natCast]
    rw [hmean, htotal]

end CountingMatroid.Analysis.RecordedObservationTrajectory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · proved · constructed the operational recorded trace, proved exact charged-fold projection and all accumulator sums, and recovered a state list and every empirical mean from each successful observation output.
-/
