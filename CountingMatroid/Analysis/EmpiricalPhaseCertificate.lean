import CountingMatroid.Analysis.FirstPhaseFailure
import CountingMatroid.Analysis.BoundedRunPhaseHistory
import CountingMatroid.Analysis.PhaseResourcePrimitives
import CountingMatroid.Analysis.RelativeObservationBounds
import CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

set_option autoImplicit false

namespace CountingMatroid.Analysis.EmpiricalPhaseCertificate

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.FinishPhaseEmpiricalUpdate

/-- INTERNAL: Raw empirical mean estimates and the exact stationary type
identity needed by the deterministic finishing step. The means need not be
estimates from independent samples. The ideal-multiplier drift is retained
explicitly rather than inferred from accurate empirical ratios.
TEXLINE: main.tex:1241-1270 -/
def ObservationEstimates {n : ℕ} (s : AnnealingSchedule)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (R : ℚ) (ideal nextIdeal : Multipliers n) : Prop :=
  ∃ pZero : ℚ, ∃ pDefect : DefectIndex n → ℚ,
    0 < s.observations ∧ 0 < pZero ∧ 0 < R ∧
    RelativeEstimate s.η pZero
      ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) ∧
    RelativeEstimate s.η (pZero * R)
      (observed.numeratorSum / (s.observations : ℚ)) ∧
    ∀ index, 0 < weights index ∧ 0 < pDefect index ∧
      weights index * pZero / pDefect index = ideal index ∧
      (ideal index / 2 ≤ nextIdeal index ∧ nextIdeal index ≤ 2 * ideal index) ∧
      RelativeEstimate s.η (pDefect index)
        ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
          (s.observations : ℚ))

/-- INTERNAL: Raw correlated-observation estimates imply a successful actual
finish, an accurate ratio, and good next weights. This separates deterministic
learning from concentration and the finite-tape coupling.
TEXLINE: main.tex:1253-1270 -/
theorem observation_estimates_finish {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (R : ℚ) (ideal nextIdeal : Multipliers n)
    (hη : 0 ≤ s.η) (hηsmall : s.η ≤ 1 / 3)
    (hobs : ObservationEstimates s weights observed R ideal nextIdeal) :
    ∃ ratio : ℚ, ∃ nextWeights : Multipliers n,
      (finishPhase s j weights observed).val = some (ratio, nextWeights) ∧
      (1 - s.η) / (1 + s.η) ≤ ratio / R ∧
      ratio / R ≤ (1 + s.η) / (1 - s.η) ∧
      (j + 1 < s.L → ∀ index,
        nextIdeal index / 4 ≤ nextWeights index ∧
        nextWeights index ≤ 4 * nextIdeal index) := by
  obtain ⟨pZero, pDefect, hN, hpZero, hR, hz, hu, hd⟩ := hobs
  have hηlt : s.η < 1 := by linarith
  have hNq : (0 : ℚ) < s.observations := by exact_mod_cast hN
  have hNz : (s.observations : ℚ) ≠ 0 := hNq.ne'
  obtain ⟨_, hzeroPos, hl, hh⟩ := relative_quotient_bounds s.η
    (pZero * R) pZero
    (observed.numeratorSum / (s.observations : ℚ))
    ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
    hη hηlt (mul_pos hpZero hR) hpZero hu hz
  have hzero : 0 < observed.counts .transversal := by
    have h := (div_pos_iff_of_pos_right hNq).mp hzeroPos
    exact_mod_cast h
  have hdefect : ∀ index : DefectIndex n,
      0 < observed.counts (.defect index.emptyPair index.fullPair) := by
    intro index
    have hmean := (hd index).2.1
    have he := (hd index).2.2.2.2
    have hpos : 0 < (observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
        (s.observations : ℚ) :=
      (mul_pos (by linarith : 0 < 1 - s.η) hmean).trans_le he.1
    have h := (div_pos_iff_of_pos_right hNq).mp hpos
    exact_mod_cast h
  let ratio := observed.numeratorSum / (observed.counts .transversal : ℚ)
  let nextWeights := empiricalWeights s j weights observed
  refine ⟨ratio, nextWeights,
    finishPhase_empirical_update s j weights observed hN hzero hdefect, ?_, ?_, ?_⟩
  · have he : (observed.numeratorSum / (s.observations : ℚ)) /
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) = ratio := by
      dsimp [ratio]
      field_simp
    simpa only [he, mul_div_cancel_left₀ R hpZero.ne'] using hl
  · have he : (observed.numeratorSum / (s.observations : ℚ)) /
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) = ratio := by
      dsimp [ratio]
      field_simp
    simpa only [he, mul_div_cancel_left₀ R hpZero.ne'] using hh
  · intro hj index
    obtain ⟨hw, hpi, hideal, hdrift, he⟩ := hd index
    have hb := learned_multiplier_bounds s.η (weights index) pZero (pDefect index)
      ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
      ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
        (s.observations : ℚ)) (ideal index) (nextIdeal index)
      hη hηsmall hw hpZero hpi hz he hideal hdrift
    have hformula : nextWeights index = weights index *
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) /
        ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
          (s.observations : ℚ)) := by
      dsimp [nextWeights, empiricalWeights]
      rw [if_pos hj]
      field_simp
    rwa [← hformula] at hb

/-- INTERNAL: A phase-level certificate exposing the restart endpoint and
raw empirical means before finishing. Its mean identities and drift are
mathematical obligations; no phase-success probability is assumed here.
TEXLINE: main.tex:1207-1285 -/
def RawPhaseEstimates {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  let ideal := fun a index => C a /
    FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
  ∃ current : AnnealingCursor n, ∃ start : PairedSet n × ℕ,
    ∃ observed : ObservationCursor n,
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
    FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
    (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val = some start ∧
    (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val =
      some observed ∧
    ObservationEstimates s current.currentWeights observed
      (C (j + 1) / C j) (ideal j) (ideal (j + 1))

/-- INTERNAL: Raw restart/observation estimates certify the actual phase,
including its product and stored-table updates. The stochastic bound can
therefore target raw estimation errors rather than assume learned weights
and accurate finish results simultaneously.
TEXLINE: main.tex:1253-1285 -/
theorem raw_phase_certified {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (hη : 0 ≤ s.η) (hηsmall : s.η ≤ 1 / 3)
    (hraw : RawPhaseEstimates r o₁ o₂ tape s j) :
    FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j := by
  obtain ⟨current, start, observed, hcurrent, hgood, hstart, hobs, hest⟩ := hraw
  obtain ⟨ratio, nextWeights, hfinish, hl, hu, hnextGood⟩ :=
    observation_estimates_finish s j current.currentWeights observed _ _ _
      hη hηsmall hest
  let next : AnnealingCursor n :=
    ⟨if j + 1 < s.L then
        (learnedWeightWrite current.tables (j + 1) s.L nextWeights).val
      else current.tables,
      nextWeights, current.product * ratio, observed.bitCursor⟩
  refine ⟨ratio, hl, hu, current, next, hcurrent, ?_, rfl, hgood, ?_⟩
  · simp only [BoundedRunPhase.boundedRunPhase, Arlib.Computation.Charged.val_bind,
      BoundedRunResourceEnvelope.ratPower_value, hstart, hobs, hfinish,
      ratMul, successor, lessThan, Arlib.Computation.Charged.val_opMany,
      Arlib.Computation.Charged.val_op]
    by_cases hj : j + 1 < s.L <;> simp [hj, next]
  · intro hj
    have htables := hgood.1
    have hw := hnextGood hj
    constructor
    · intro a ha index
      dsimp [next]
      rw [if_pos hj]
      simp only [learnedWeightWrite, Arlib.Computation.Charged.val_opMany]
      by_cases heq : a = j + 1
      · subst a
        simpa using hw index
      · rw [if_neg heq]
        exact htables a (by omega) index
    · exact hw

end CountingMatroid.Analysis.EmpiricalPhaseCertificate

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · raw empirical mean estimates imply the actual phase
  certificate through exact finishing, ratio arithmetic, and learned-table
  preservation. Concentration and finite-tape coupling remain in the parent.
-/
