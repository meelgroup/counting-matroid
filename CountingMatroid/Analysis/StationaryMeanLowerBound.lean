import CountingMatroid.Analysis.PhaseObservationExperiment
import Mathlib.Data.Fintype.Card

set_option autoImplicit false

namespace CountingMatroid.Analysis.StationaryMeanLowerBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Enumerate the concrete off-diagonal type indices. -/
noncomputable instance defectIndexFintype (n : ℕ) : Fintype (DefectIndex n) :=
  Fintype.ofInjective (fun index => (index.emptyPair, index.fullPair)) (by
    rintro ⟨i, k, h⟩ ⟨i', k', h'⟩ he
    simpa only [Prod.mk.injEq, DefectIndex.mk.injEq] using he)

/-- INTERNAL: Bounding off-diagonal types by all ordered pairs also covers
n=1, where there are no defect types.
TEXLINE: main.tex:1256-1263 -/
theorem defect_index_card_le (n : ℕ) : Fintype.card (DefectIndex n) ≤ n ^ 2 := by
  have hi : Function.Injective (fun index : DefectIndex n =>
      (index.emptyPair, index.fullPair)) := by
    rintro ⟨i, k, h⟩ ⟨i', k', h'⟩ he
    simpa only [Prod.mk.injEq, DefectIndex.mk.injEq] using he
  simpa only [Fintype.card_prod, Fintype.card_fin, pow_two] using
    Fintype.card_le_of_injective _ hi

/-- INTERNAL: Partition the operational normalizer into its transversal
and off-diagonal class masses. Rejected and diagonal states have zero weight.
TEXLINE: main.tex:721-735 -/
theorem normalizer_decomposition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    normalizer r o₁ o₂ q w = TransversalPartition.partitionSum r o₁ o₂ q +
      ∑ index : DefectIndex n, w index * FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
  classical
  obtain ⟨hZ, ht, _, hd⟩ := stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hpartition (state : PairedSet n) :
      stateWeight r o₁ o₂ q w state =
        (if (classifyState state).val = .transversal then stateWeight r o₁ o₂ q w state else 0) +
        ∑ index : DefectIndex n,
          if (classifyState state).val = .defect index.emptyPair index.fullPair
          then stateWeight r o₁ o₂ q w state else 0 := by
    cases hk : (classifyState state).val with
    | invalid => simp [stateWeight, hk, weightOfKind]
    | transversal => simp
    | defect i k =>
      by_cases hik : i ≠ k
      · let index : DefectIndex n := ⟨i, k, hik⟩
        have hsum : (∑ a : DefectIndex n,
            if StateKind.defect i k = .defect a.emptyPair a.fullPair
            then stateWeight r o₁ o₂ q w state else 0) = stateWeight r o₁ o₂ q w state := by
          rw [Finset.sum_eq_single index]
          · simp [index]
          · intro a _ ha
            apply if_neg
            intro he
            have hpair := StateKind.defect.inj he
            apply ha
            cases a
            simp_all [index]
          · simp
        have hneq : StateKind.defect i k ≠ StateKind.transversal := by
          intro he
          cases he
        rw [if_neg hneq, zero_add]
        exact hsum.symm
      · have hzero : stateWeight r o₁ o₂ q w state = 0 := by
          simp [stateWeight, hk, weightOfKind, hik]
        simp [hzero]
  have hmass := congrArg (fun x : ℚ => x * normalizer r o₁ o₂ q w) ht
  have hdef (index : DefectIndex n) :=
    congrArg (fun x : ℚ => x * normalizer r o₁ o₂ q w) (hd index)
  simp only [typeMean, div_mul_cancel₀ _ hZ.ne'] at hmass hdef
  calc
    normalizer r o₁ o₂ q w = ∑ state : PairedSet n,
        ((if (classifyState state).val = .transversal then stateWeight r o₁ o₂ q w state else 0) +
          ∑ index : DefectIndex n,
            if (classifyState state).val = .defect index.emptyPair index.fullPair
            then stateWeight r o₁ o₂ q w state else 0) :=
      Finset.sum_congr rfl (fun state _ => hpartition state)
    _ = _ := by
      rw [Finset.sum_add_distrib, hmass, Finset.sum_comm]
      simp_rw [hdef]

/-- PAPER: main.tex:1241-1255
Every type mean and the ratio-observable mean is at least 1/(20 n²)
under good multipliers. The proof is over the actual normalized program
weights and uses the concrete schedule's factor-two partition step. -/
theorem observable_mean_lower (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (current : AnnealingCursor n)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (index : Observable n) :
    1 / (20 * (n : ℚ) ^ 2) ≤ observableMean r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current index := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let q := s.ρ ^ j
  let C := TransversalPartition.partitionSum r o₁ o₂ q
  let w := current.currentWeights
  let Z := normalizer r o₁ o₂ q w
  have hρ := (AnnealingPartitionDrift.schedule_power_lower n p hn).1
  have hq : 0 < q := pow_pos hρ j
  have hC : 0 < C :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
  have hD (a : DefectIndex n) : 0 < FirstPhaseFailure.defectPartition r o₁ o₂ q a :=
    DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq a
  have hw (a : DefectIndex n) : 0 < w a :=
    (div_pos (div_pos hC (hD a)) (by norm_num : (0 : ℚ) < 4)).trans_le (hgood.2 a).1
  obtain ⟨hZ, ht, hu, hd⟩ := stationary_mean_identities r o₁ o₂ q s.ρ w hq hw
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hupper (a : DefectIndex n) : w a * FirstPhaseFailure.defectPartition r o₁ o₂ q a ≤ 4 * C := by
    have h := mul_le_mul_of_nonneg_right (hgood.2 a).2 (hD a).le
    change w a * FirstPhaseFailure.defectPartition r o₁ o₂ q a ≤
      (4 * (C / FirstPhaseFailure.defectPartition r o₁ o₂ q a)) *
        FirstPhaseFailure.defectPartition r o₁ o₂ q a at h
    have heq : (4 * (C / FirstPhaseFailure.defectPartition r o₁ o₂ q a)) *
        FirstPhaseFailure.defectPartition r o₁ o₂ q a = 4 * C := by
      field_simp [(hD a).ne']
    rwa [heq] at h
  have hZupper : Z ≤ 5 * (n : ℚ) ^ 2 * C := by
    dsimp only [Z]
    rw [normalizer_decomposition r o₁ o₂ q w hq hw]
    have hsum := Finset.sum_le_sum (fun a (_ : a ∈ Finset.univ) => hupper a)
    have hcard : (Fintype.card (DefectIndex n) : ℚ) ≤ (n : ℚ) ^ 2 := by
      exact_mod_cast defect_index_card_le n
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at hsum
    nlinarith [mul_le_mul_of_nonneg_right hcard (by positivity : (0 : ℚ) ≤ 4 * C)]
  have hsmall : 1 / (20 * (n : ℚ) ^ 2) ≤ (C / 4) / Z := by
    apply (le_div_iff₀ hZ).mpr
    rw [div_mul_eq_mul_div, one_mul]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 20 * (n : ℚ) ^ 2)).mpr
    nlinarith [hZupper]
  have htype : 1 / (20 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w .transversal := by
    rw [ht]
    exact hsmall.trans (div_le_div_of_nonneg_right (by linarith : C / 4 ≤ C) hZ.le)
  cases index with
  | inl b =>
    cases b with
    | false => exact htype
    | true =>
      change 1 / (20 * (n : ℚ) ^ 2) ≤ numeratorMean r o₁ o₂ q s.ρ w
      rw [hu]
      have hnext := (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).2.1
      have hpower : q * s.ρ = s.ρ ^ (j + 1) := (pow_succ s.ρ j).symm
      rw [hpower]
      exact hsmall.trans (div_le_div_of_nonneg_right (by linarith :
        C / 4 ≤ TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1))) hZ.le)
  | inr pair =>
    rcases pair with ⟨i, k⟩
    by_cases hik : i = k
    · simpa only [observableMean, if_pos hik] using htype
    · simp only [observableMean, if_neg hik]
      change 1 / (20 * (n : ℚ) ^ 2) ≤ typeMean r o₁ o₂ q w (.defect i k)
      let a : DefectIndex n := ⟨i, k, hik⟩
      rw [hd a]
      have hlow := mul_le_mul_of_nonneg_right (hgood.2 a).1 (hD a).le
      have heq : (C / FirstPhaseFailure.defectPartition r o₁ o₂ q a / 4) *
          FirstPhaseFailure.defectPartition r o₁ o₂ q a = C / 4 := by
        field_simp [(hD a).ne']
      rw [heq] at hlow
      exact hsmall.trans (div_le_div_of_nonneg_right hlow hZ.le)

end CountingMatroid.Analysis.StationaryMeanLowerBound
