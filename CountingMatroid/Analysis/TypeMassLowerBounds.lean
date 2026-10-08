import CountingMatroid.Analysis.PhaseMeanCertificate

set_option autoImplicit false

namespace CountingMatroid.Analysis.TypeMassLowerBounds

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: Split the operational state-weight normalizer into its
transversal mass and the masses of all off-diagonal defect classes. The
invalid and diagonal classifier branches have weight zero.
TEXLINE: main.tex:721-744 -/
theorem normalizer_class_sum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    normalizer r o₁ o₂ q w =
      TransversalPartition.partitionSum r o₁ o₂ q +
        ∑ i : Fin n, ∑ k : Fin n, if h : i ≠ k then
          w ⟨i, k, h⟩ * FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, h⟩
        else 0 := by
  classical
  let W := stateWeight r o₁ o₂ q w
  have hsplit (state : PairedSet n) : W state =
      (if (classifyState state).val = .transversal then W state else 0) +
      ∑ i : Fin n, ∑ k : Fin n,
        if h : i ≠ k then
          if (classifyState state).val = .defect i k then W state else 0
        else 0 := by
    cases hk : (classifyState state).val with
    | invalid => simp [W, stateWeight, hk, weightOfKind]
    | transversal => simp [hk]
    | defect i k =>
      by_cases h : i ≠ k
      · have hterm (a b : Fin n) :
            (if h' : a ≠ b then
              if StateKind.defect i k = StateKind.defect a b then W state else 0
            else 0) = if a = i then (if b = k then W state else 0) else 0 := by
          by_cases ha : a = i <;> by_cases hb : b = k
          all_goals split_ifs <;> simp_all
        rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun b _ => hterm a b))]
        simp [hk]
      · simp [W, stateWeight, hk, weightOfKind, h]
  obtain ⟨hZ, hzero, _, hdefect⟩ :=
    stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hzeroSum : (∑ state : PairedSet n,
      if (classifyState state).val = .transversal then W state else 0) =
      TransversalPartition.partitionSum r o₁ o₂ q := by
    apply (div_left_inj' hZ.ne').mp
    exact hzero
  have hdefectSum (index : DefectIndex n) :
      (∑ state : PairedSet n,
        if (classifyState state).val = .defect index.emptyPair index.fullPair then
          W state else 0) =
      w index * FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
    apply (div_left_inj' hZ.ne').mp
    exact hdefect index
  unfold normalizer
  rw [Finset.sum_congr rfl (fun state _ => hsplit state), Finset.sum_add_distrib,
    hzeroSum]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  by_cases h : i ≠ k
  · simp only [dif_pos h]
    exact hdefectSum ⟨i, k, h⟩
  · simp [h]

/-- PAPER: main.tex:736-744
Good multipliers give polynomial lower bounds for every operational type
mean, including the empty defect family when `n = 1`. -/
theorem good_type_mass_bounds {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hq : 0 < q)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index)) :
    normalizer r o₁ o₂ q w ≤
      5 * (n : ℚ) ^ 2 * TransversalPartition.partitionSum r o₁ o₂ q ∧
    1 / (5 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w .transversal ∧
    ∀ index : DefectIndex n, 1 / (20 * (n : ℚ) ^ 2) ≤
      typeMean r o₁ o₂ q w (.defect index.emptyPair index.fullPair) := by
  classical
  let C := TransversalPartition.partitionSum r o₁ o₂ q
  let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
  have hC : 0 < C := by
    apply Finset.sum_pos
    · intro A _
      exact pow_pos hq _
    · exact Finset.univ_nonempty
  have hD (index : DefectIndex n) : 0 < D index :=
    DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
  have hw (index : DefectIndex n) : 0 < w index :=
    (div_pos (div_pos hC (hD index)) (by norm_num : (0 : ℚ) < 4)).trans_le
      (hgood index).1
  have hclass (index : DefectIndex n) :
      C / 4 ≤ w index * D index ∧ w index * D index ≤ 4 * C := by
    have hlo := mul_le_mul_of_nonneg_right (hgood index).1 (hD index).le
    have hhi := mul_le_mul_of_nonneg_right (hgood index).2 (hD index).le
    dsimp only [C, D] at *
    constructor
    · convert hlo using 1 <;> first | rfl | field_simp [(hD index).ne']
    · convert hhi using 1 <;> first | rfl | field_simp [(hD index).ne']
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hbound : normalizer r o₁ o₂ q w ≤ 5 * (n : ℚ) ^ 2 * C := by
    rw [normalizer_class_sum r o₁ o₂ q w hq hw]
    calc
      C + (∑ i : Fin n, ∑ k : Fin n,
          if h : i ≠ k then w ⟨i, k, h⟩ * D ⟨i, k, h⟩ else 0) ≤
          C + ∑ _i : Fin n, ∑ _k : Fin n, 4 * C := by
        apply add_le_add le_rfl
        apply Finset.sum_le_sum
        intro i _
        apply Finset.sum_le_sum
        intro k _
        split_ifs with h
        · exact (hclass ⟨i, k, h⟩).2
        · positivity
      _ = (1 + 4 * (n : ℚ) ^ 2) * C := by simp; ring
      _ ≤ 5 * (n : ℚ) ^ 2 * C := by nlinarith [hC.le]
  obtain ⟨hZ, hz, _, hd⟩ := stationary_mean_identities r o₁ o₂ q 1 w hq hw
  refine ⟨hbound, ?_, ?_⟩
  · rw [hz]
    apply (div_le_div_iff₀ (by positivity) hZ).mpr
    simpa only [one_mul, mul_comm] using hbound
  · intro index
    rw [hd index]
    apply (div_le_div_iff₀ (by positivity) hZ).mpr
    have hb := mul_le_mul_of_nonneg_right (hclass index).1
      (by positivity : (0 : ℚ) ≤ 20 * (n : ℚ) ^ 2)
    nlinarith

/-- PAPER: main.tex:1248-1249
The annealing numerator's stationary mean also has the polynomial lower
bound used to turn absolute empirical error into relative error. -/
theorem good_numerator_mean_lower_bound (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (w : Multipliers n) (hn : 0 < n)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) /
        FirstPhaseFailure.defectPartition r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) /
        FirstPhaseFailure.defectPartition r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) index)) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    1 / (20 * (n : ℚ) ^ 2) ≤ numeratorMean r o₁ o₂ (s.ρ ^ j) s.ρ w := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hq : 0 < s.ρ ^ j :=
    pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  obtain ⟨hC, hstep, _⟩ := AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j
  have hw (index : DefectIndex n) : 0 < w index :=
    (div_pos (div_pos hC
      (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (s.ρ ^ j) hq index))
      (by norm_num : (0 : ℚ) < 4)).trans_le (hgood index).1
  obtain ⟨hZ, _, hU, _⟩ := stationary_mean_identities r o₁ o₂ (s.ρ ^ j) s.ρ w hq hw
  have hbound := (good_type_mass_bounds r o₁ o₂ (s.ρ ^ j) w hn hq hgood).1
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  change 1 / (20 * (n : ℚ) ^ 2) ≤ numeratorMean r o₁ o₂ (s.ρ ^ j) s.ρ w
  rw [hU, ← pow_succ]
  apply (div_le_div_iff₀ (by positivity) hZ).mpr
  simp only [one_mul]
  have hscaled := mul_le_mul_of_nonneg_left hstep
    (by positivity : (0 : ℚ) ≤ 20 * (n : ℚ) ^ 2)
  nlinarith [mul_nonneg (sq_nonneg (n : ℚ)) hC.le]

end CountingMatroid.Analysis.TypeMassLowerBounds
