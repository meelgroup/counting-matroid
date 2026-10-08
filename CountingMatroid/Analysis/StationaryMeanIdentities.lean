import CountingMatroid.Analysis.TransversalClassPartition
import CountingMatroid.Analysis.DefectPartitionPositive
import CountingMatroid.Analysis.BoundedRunResourceEnvelope

set_option autoImplicit false

namespace CountingMatroid.Analysis.StationaryMeanIdentities

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The program's exact Metropolis state weight, extended by zero
to states its classifier rejects. This definition uses the executable scans.
TEXLINE: main.tex:721-728,746-751 -/
noncomputable def stateWeight {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n) : ℚ :=
  (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val.getD 0

/-- INTERNAL: Normalizing constant of the finite state-weight law. No
claim about a capped transition's stationarity is made by this definition.
TEXLINE: main.tex:721-728 -/
noncomputable def normalizer {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) : ℚ :=
  ∑ state : PairedSet n, stateWeight r o₁ o₂ q weights state

/-- INTERNAL: Type-indicator mean under the normalized state weights.
TEXLINE: main.tex:1241-1247 -/
noncomputable def typeMean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (kind : StateKind n) : ℚ :=
  (∑ state : PairedSet n,
    if (classifyState state).val = kind then stateWeight r o₁ o₂ q weights state else 0) /
      normalizer r o₁ o₂ q weights

/-- INTERNAL: Mean of the same observable added by `recordObservation`:
zero on defects and the cooling factor to the paired deficiency on transversals.
TEXLINE: main.tex:1181-1187,1241-1247 -/
noncomputable def numeratorMean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q ρ : ℚ) (weights : Multipliers n) : ℚ :=
  (∑ state : PairedSet n,
    if (classifyState state).val = .transversal then
      stateWeight r o₁ o₂ q weights state *
        ρ ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0) / normalizer r o₁ o₂ q weights

/-- INTERNAL: Evaluate the exact program weight on an accepted transversal.
TEXLINE: main.tex:721-728 -/
private theorem state_weight_transversal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (hkind : (classifyState state).val = .transversal) :
    stateWeight r o₁ o₂ q weights state =
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
  simp [stateWeight, hkind, weightOfKind, natSub,
    BoundedRunResourceEnvelope.ratPower_value]

/-- INTERNAL: Evaluate the exact program weight on an accepted ordered defect.
TEXLINE: main.tex:721-728 -/
private theorem state_weight_defect {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (index : DefectIndex n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    stateWeight r o₁ o₂ q weights state = weights index *
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
  simp [stateWeight, hkind, weightOfKind, index.distinct, natSub,
    BoundedRunResourceEnvelope.ratPower_value, multiplierRead, ratMul]

/-- INTERNAL: The normalized operational state weights have the paper's
type and annealing-observable mean identities. Stationarity for the ideal
Metropolis kernel and coupling to the capped draws remain separate obligations.
TEXLINE: main.tex:721-728,1241-1247 -/
theorem stationary_mean_identities {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q ρ : ℚ) (weights : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < weights index) :
    let Z := normalizer r o₁ o₂ q weights
    0 < Z ∧
      typeMean r o₁ o₂ q weights .transversal =
        TransversalPartition.partitionSum r o₁ o₂ q / Z ∧
      numeratorMean r o₁ o₂ q ρ weights =
        TransversalPartition.partitionSum r o₁ o₂ (q * ρ) / Z ∧
      ∀ index, typeMean r o₁ o₂ q weights
        (.defect index.emptyPair index.fullPair) =
        weights index * FirstPhaseFailure.defectPartition r o₁ o₂ q index / Z := by
  classical
  have hnonneg (state : PairedSet n) : 0 ≤ stateWeight r o₁ o₂ q weights state := by
    cases hkind : (classifyState state).val with
    | invalid => simp [stateWeight, hkind, weightOfKind]
    | transversal =>
        rw [state_weight_transversal r o₁ o₂ q weights state hkind]
        exact (pow_pos hq _).le
    | defect i j =>
        by_cases hij : i ≠ j
        · rw [state_weight_defect r o₁ o₂ q weights state ⟨i, j, hij⟩ hkind]
          exact (mul_pos (hw _) (pow_pos hq _)).le
        · simp [stateWeight, hkind, weightOfKind, hij]
  have hCsum : (∑ state : PairedSet n,
      if (classifyState state).val = .transversal then
        stateWeight r o₁ o₂ q weights state else 0) =
      TransversalPartition.partitionSum r o₁ o₂ q := by
    rw [← TransversalClassPartition.transversal_class_partition r o₁ o₂ q]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs with hkind
    · exact state_weight_transversal r o₁ o₂ q weights state hkind
    · rfl
  have hCpos : 0 < TransversalPartition.partitionSum r o₁ o₂ q := by
    apply Finset.sum_pos
    · intro A _
      exact pow_pos hq _
    · exact Finset.univ_nonempty
  have hCbound : TransversalPartition.partitionSum r o₁ o₂ q ≤
      normalizer r o₁ o₂ q weights := by
    rw [← hCsum]
    apply Finset.sum_le_sum
    intro state _
    split_ifs
    · exact le_rfl
    · exact hnonneg state
  have hZ : 0 < normalizer r o₁ o₂ q weights := hCpos.trans_le hCbound
  refine ⟨hZ, ?_, ?_, ?_⟩
  · exact congrArg (· / normalizer r o₁ o₂ q weights) hCsum
  · unfold numeratorMean
    apply congrArg (· / normalizer r o₁ o₂ q weights)
    rw [← TransversalClassPartition.transversal_class_partition r o₁ o₂ (q * ρ)]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs with hkind
    · rw [state_weight_transversal r o₁ o₂ q weights state hkind, mul_pow]
    · rfl
  · intro index
    unfold typeMean
    apply congrArg (· / normalizer r o₁ o₂ q weights)
    unfold FirstPhaseFailure.defectPartition
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs with hkind
    · exact state_weight_defect r o₁ o₂ q weights state index hkind
    · exact (mul_zero _).symm

end CountingMatroid.Analysis.StationaryMeanIdentities
