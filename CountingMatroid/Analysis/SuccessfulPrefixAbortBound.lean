import CountingMatroid.Analysis.FinitePhaseExecutionAbort
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.SuccessfulPrefixCursor
import CountingMatroid.Analysis.FinitePhaseEstimationBound
import CountingMatroid.Analysis.ConditionalRestartAbortMass
import CountingMatroid.Analysis.ConditionalObservationAbortMass
import CountingMatroid.Analysis.ScheduleAbortBudget

set_option autoImplicit false

/-!
The conditional execution-abort estimate needed for the lower-tail proof.
The completion-failure characterization and the finite union-bound assembly
are proved. The quantitative estimate uses the separate conditional restart
and observation abort bounds; their operational coupling proofs remain open
in their respective modules. All events retain the actual program outputs.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Operational completion can fail only because no observation
output was produced, or because the produced cursor fails the deterministic
good-weight/nonempty-sample checks. No stochastic estimate is asserted.
TEXLINE: main.tex:1163-1187,1207-1266 -/
theorem observation_not_completed_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) :
    ¬ ObservationCompleted r o₁ o₂ tape s j ↔
      phaseObservationData r o₁ o₂ tape s j = none ∨
      ∃ current observed,
        phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
        ¬ (FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
          0 < s.observations) := by
  cases hdata : phaseObservationData r o₁ o₂ tape s j with
  | none => simp [ObservationCompleted, hdata]
  | some pair =>
      rcases pair with ⟨current, observed⟩
      simp [ObservationCompleted, hdata]

/-- INTERNAL: With certified earlier phases, incomplete observation data
means an actual restart abort or an actual observation abort after restart.
The good-table and nonempty-sample checks cannot contribute another event.
TEXLINE: main.tex:1207-1239,1392-1421 -/
theorem observation_failure_cases {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (tape : ℕ → Bool) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hprevious : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) a)
    (hbad : ¬ ObservationCompleted r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) j) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    ∃ current : AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
      ((restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val = none ∨
        ∃ start, (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val =
          some start ∧ (observePhase r o₁ o₂ tape s (s.ρ ^ j)
            current.currentWeights start).val = none) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  obtain ⟨current, hh, hg⟩ := certified_history_has_good_cursor r o₁ o₂ p tape j hj hprevious
  refine ⟨current, hh, ?_⟩
  cases hs : (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val with
  | none => exact Or.inl rfl
  | some start =>
      refine Or.inr ⟨start, rfl, ?_⟩
      cases ho : (observePhase r o₁ o₂ tape s (s.ρ ^ j)
          current.currentWeights start).val with
      | none => rfl
      | some observed =>
          exfalso
          apply hbad
          exact ⟨current, observed,
            (observation_data_iff r o₁ o₂ tape s j current observed).mpr ⟨hh, start, hs, ho⟩,
            hg, (FinitePhaseEstimationBound.schedule_estimation_budget n p hn).2.1⟩

/-- INTERNAL: Bound the abort mass after fixing a consumed prefix of a
successful history. This includes restart-cap exhaustion and all capped
rejection draws, with finite-block coverage proved as part of the estimate.
The draw budget is 1/[16(L+1)] and the restart-tail budget is 1/[32(L+1)].
TEXLINE: main.tex:1207-1239,1392-1421 -/
theorem conditional_successful_prefix_abort_mass (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ¬ ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 3 / (32 * ((s.L : ENNReal) + 1)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let tape := fun suffix : List Bool => fun i : ℕ => ((pref ++ suffix)[i]?).getD false
  let previous := fun suffix : List Bool =>
    ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ (tape suffix) s a
  let restartBad : Set (List Bool) := {suffix | suffix.length = t ∧ previous suffix ∧
    ∃ current : AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ (tape suffix) s j = some current ∧
      (restartPhase r o₁ o₂ (tape suffix) s current.tables j current.bitCursor).val = none}
  let observationBad : Set (List Bool) := {suffix | suffix.length = t ∧ previous suffix ∧
    ∃ current : AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ (tape suffix) s j = some current ∧
      ∃ start, (restartPhase r o₁ o₂ (tape suffix) s current.tables j
        current.bitCursor).val = some start ∧
        (observePhase r o₁ o₂ (tape suffix) s (s.ρ ^ j)
          current.currentWeights start).val = none}
  let bad : Set (List Bool) := {suffix | suffix.length = t ∧ previous suffix ∧
    ¬ ObservationCompleted r o₁ o₂ (tape suffix) s j}
  have hcover : bad ⊆ restartBad ∪ observationBad := by
    intro suffix hsuffix
    obtain ⟨current, hh, hf⟩ := observation_failure_cases r o₁ o₂ p hn
      (tape suffix) j hj hsuffix.2.1 hsuffix.2.2
    rcases hf with hr | ⟨start, hr, ho⟩
    · exact Or.inl ⟨hsuffix.1, hsuffix.2.1, current, hh, hr⟩
    · exact Or.inr ⟨hsuffix.1, hsuffix.2.1, current, hh, start, hr, ho⟩
  have hrfinite : restartBad.Finite :=
    (List.finite_length_eq Bool t).subset (fun _ h => h.1)
  have hofinite : observationBad.Finite :=
    (List.finite_length_eq Bool t).subset (fun _ h => h.1)
  have hcard : bad.ncard ≤ restartBad.ncard + observationBad.ncard :=
    (Set.ncard_le_ncard hcover (hrfinite.union hofinite)).trans
      (Set.ncard_union_le restartBad observationBad)
  have hrmass := ConditionalRestartAbortMass.conditional_restart_abort_mass
    n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix
  have homass := ConditionalObservationAbortMass.conditional_observation_abort_mass
    n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix
  change (restartBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ _ at hrmass
  change (observationBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ _ at homass
  change (bad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ _
  calc
    _ ≤ ((restartBad.ncard + observationBad.ncard : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ t := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) bot_le
    _ = (restartBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t +
        (observationBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      rw [Nat.cast_add, add_mul]
    _ ≤ ENNReal.ofReal (((s.L : ℚ) / (100 * ((s.L : ℚ) + 1) ^ 2) +
        3 * (s.restartCap : ℚ) * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) +
        ENNReal.ofReal ((3 * (s.observations : ℚ) *
          (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := add_le_add hrmass homass
    _ = ENNReal.ofReal (((s.L : ℚ) / (100 * ((s.L : ℚ) + 1) ^ 2) +
        3 * (s.restartCap : ℚ) * (1 / 2 : ℚ) ^ s.drawTrials +
        3 * (s.observations : ℚ) * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
      conv_rhs => rw [Rat.cast_add]
      exact (ENNReal.ofReal_add (by positivity) (by positivity)).symm
    _ ≤ ENNReal.ofReal ((3 / (32 * ((s.L : ℚ) + 1)) : ℚ) : ℝ) := by
      apply ENNReal.ofReal_le_ofReal
      exact_mod_cast ScheduleAbortBudget.schedule_abort_budget n p hn
    _ = 3 / (32 * ((s.L : ENNReal) + 1)) := by
      push_cast
      rw [ENNReal.ofReal_div_of_pos (by positivity)]
      simp [ENNReal.ofReal_mul, ENNReal.ofReal_add]

end CountingMatroid.Analysis.SuccessfulPrefixAbortBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r24 · assembled · covered completion failure by the actual restart and post-restart observation abort events; combined their existing conditional bounds using the proved schedule budget. The two imported quantitative coupling proofs remain open in their owning modules; no new open helper was introduced.

* r23 · reduced · proved `successful_prefix_has_good_cursor`, including the exact min(cursor, blockLength) prefix length; extracting fixed good tables does not establish cursor coverage or a restart tail.

* r23 · attempted · rewrote completion failure into absent data or failed invariant checks; restart-return expectation, capped-draw coupling and finite cursor/width coverage remain open.
-/
