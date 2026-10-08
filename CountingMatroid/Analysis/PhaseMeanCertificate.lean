import CountingMatroid.Analysis.AnnealingPartitionDrift
import CountingMatroid.Analysis.EmpiricalPhaseCertificate
import CountingMatroid.Analysis.StationaryMeanIdentities

set_option autoImplicit false

/-!
The raw phase boundary requires relative empirical errors about the normalized
operational state weights. `StationaryMeanIdentities` supplies their exact
type and annealing-observable mean identities using the classifier's
transversal reindexing. Positivity of the true ratio and drift of the ideal
multipliers are deterministic consequences of the concrete schedule and
partition sums, proved in `AnnealingPartitionDrift`. They need not be included
in an event whose probability is estimated. No stochastic estimate is asserted
by this module.
-/

namespace CountingMatroid.Analysis.PhaseMeanCertificate

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RelativeObservationBounds
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: The actual phase's restart and empirical mean estimates,
retaining its good prior history. Means are fixed by the actual normalized
state weights, rather than chosen existentially. Mean identities, positivity,
and ideal-multiplier drift are deterministic facts supplied by the bridge.
TEXLINE: main.tex:1141-1145,1207-1270 -/
def RawPhaseMeans {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  ∃ current : AnnealingCursor n, ∃ start : PairedSet n × ℕ,
    ∃ observed : ObservationCursor n,
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
    FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
    (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val = some start ∧
    (observePhase r o₁ o₂ tape s (s.ρ ^ j) current.currentWeights start).val =
      some observed ∧
    0 < s.observations ∧
      RelativeEstimate s.η
        (typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights .transversal)
        ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) ∧
      RelativeEstimate s.η
        (numeratorMean r o₁ o₂ (s.ρ ^ j) s.ρ current.currentWeights)
        (observed.numeratorSum / (s.observations : ℚ)) ∧
      ∀ index : DefectIndex n, RelativeEstimate s.η
        (typeMean r o₁ o₂ (s.ρ ^ j) current.currentWeights
          (.defect index.emptyPair index.fullPair))
          ((observed.counts (.defect index.emptyPair index.fullPair) : ℚ) /
            (s.observations : ℚ))

/-- INTERNAL: Relative empirical errors certify the raw phase estimates;
the normalized state-weight identities supply the true means, and the schedule
supplies positivity and ideal-multiplier drift.
This bridge discharges those deterministic obligations for the phase-failure
probability proof, without assuming mixing or concentration.
TEXLINE: main.tex:1141-1145,1257-1270 -/
theorem raw_phase_means_estimates (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (tape : ℕ → Bool) (j : ℕ)
    (hmeans : RawPhaseMeans r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) j) :
    EmpiricalPhaseCertificate.RawPhaseEstimates r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) j := by
  obtain ⟨current, start, observed, hcurrent, hgood, hstart, hobs,
    hN, hz, hu, hd⟩ := hmeans
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let q := s.ρ ^ j
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  have hρ : 0 < s.ρ := (AnnealingPartitionDrift.schedule_power_lower n p hn).1
  have hC : ∀ a, 0 < C a := fun a =>
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn a).1
  have hD (index : DefectIndex n) :
      0 < FirstPhaseFailure.defectPartition r o₁ o₂ q index :=
    DefectPartitionPositive.defect_partition_pos r o₁ o₂ q (pow_pos hρ _) index
  have hw (index : DefectIndex n) : 0 < current.currentWeights index :=
    (div_pos (div_pos (hC j) (hD index)) (by norm_num : (0 : ℚ) < 4)).trans_le
      (hgood.2 index).1
  obtain ⟨hZ, hpZero, hU, hpDefect⟩ := stationary_mean_identities r o₁ o₂ q s.ρ
    current.currentWeights (pow_pos hρ _) hw
  let pZero := typeMean r o₁ o₂ q current.currentWeights .transversal
  let pDefect := fun index : DefectIndex n => typeMean r o₁ o₂ q
    current.currentWeights (.defect index.emptyPair index.fullPair)
  have hpZeroPos : 0 < pZero := by
    dsimp only [pZero]
    rw [hpZero]
    exact div_pos (hC j) hZ
  have hUratio : numeratorMean r o₁ o₂ q s.ρ current.currentWeights =
      pZero * (C (j + 1) / C j) := by
    rw [hU]
    dsimp only [pZero]
    rw [hpZero]
    have hnext : q * s.ρ = s.ρ ^ (j + 1) := (pow_succ s.ρ j).symm
    rw [hnext]
    change C (j + 1) / _ = (C j / _) * (C (j + 1) / C j)
    field_simp [(hC j).ne']
  refine ⟨current, start, observed, hcurrent, hgood, hstart, hobs,
    pZero, pDefect, hN, hpZeroPos, div_pos (hC _) (hC _), hz, ?_, ?_⟩
  · rwa [hUratio] at hu
  · intro index
    have hpi : 0 < pDefect index := by
      dsimp only [pDefect]
      rw [hpDefect index]
      exact div_pos (mul_pos (hw index) (hD index)) hZ
    refine ⟨hw index, hpi, ?_,
      AnnealingPartitionDrift.ideal_multiplier_drift n r o₁ o₂ p hn j index,
      hd index⟩
    dsimp only [pZero, pDefect]
    rw [hpZero, hpDefect index]
    change _ = TransversalPartition.partitionSum r o₁ o₂ q /
      FirstPhaseFailure.defectPartition r o₁ o₂ q index
    field_simp [hZ.ne', (hw index).ne', (hD index).ne']

end CountingMatroid.Analysis.PhaseMeanCertificate
