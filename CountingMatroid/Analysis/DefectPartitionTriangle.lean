import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

set_option autoImplicit false

/-!
The unconditional three-pair coefficient inequality used to bound the cost
of the defect transport. The q=1 case, the numerical Schur-complement
step, and the real-signature-to-rational-Schur step are proved. The parent
now uses a concrete homogeneous quadratic constructed by the paper's
derivatives and substitutions. Its operational coefficient identity and
the cited Bränden–Huh signature input remain open in their support files.
-/

namespace CountingMatroid.Analysis.DefectPartitionTriangle

open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: The numerical three-pair Schur-complement step, with its
zero final diagonal and all factors in the operational rational field.
TEXLINE: main.tex:430-449 -/
theorem three_pair_schur_bound (a c d e z : ℚ)
    (ha : 0 ≤ a) (hc : 0 < c) (he : 0 < e) (hz : 0 < z)
    (hschur : ∀ x y : ℚ,
      2 * c * (2 * a * x ^ 2 + 4 * d * x * y) ≤
        (z * x + 2 * e * y) ^ 2) : c * d ≤ z * e := by
  have h := hschur (2 * e) z
  have hdiag : 0 ≤ 2 * c * (2 * a * (2 * e) ^ 2) :=
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (sq_nonneg _))
  have hdiff : 0 ≤ (z * e - c * d) * (16 * z * e) := by
    nlinarith [hdiag]
  exact sub_nonneg.mp (nonneg_of_mul_nonneg_left hdiff (by positivity))

/-- PAPER: main.tex:397-449
The empty-assignment specialization of the paper's three-pair coefficient
inequality, evaluated with the operational paired-rank scans. -/
theorem defect_partition_triangle (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1)
    (i t k : Fin n) (hit : i ≠ t) (htk : t ≠ k) (hik : i ≠ k) :
    FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, t, hit⟩ *
      FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨t, k, htk⟩ ≤
        TransversalPartition.partitionSum r o₁ o₂ q *
          FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, hik⟩ := by
  classical
  let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
  let Z := TransversalPartition.partitionSum r o₁ o₂ q
  by_cases hqeq : q = 1
  · subst q
    rw [InitialMultipliersGood.defect_partition_one,
      InitialMultipliersGood.defect_partition_one,
      InitialMultipliersGood.defect_partition_one]
    have hC : TransversalPartition.partitionSum r o₁ o₂ 1 =
        4 * (2 : ℚ) ^ (n - 2) := by
      have h := InitialMultipliersGood.initial_ideal_multiplier r o₁ o₂ ⟨i, k, hik⟩
      rw [InitialMultipliersGood.defect_partition_one] at h
      exact (div_eq_iff (by positivity)).mp h
    rw [hC]
    nlinarith [sq_nonneg ((2 : ℚ) ^ (n - 2))]
  · have hZ : 0 < Z := by
      unfold Z TransversalPartition.partitionSum
      exact Finset.sum_pos (fun A _ => pow_pos hq _)
        (Finset.univ_nonempty)
    have hD (index : DefectIndex n) : 0 < D index :=
      DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
    have hschur : ∀ x y : ℚ,
        2 * D ⟨i, t, hit⟩ *
          (2 * D ⟨t, i, hit.symm⟩ * x ^ 2 +
            4 * D ⟨t, k, htk⟩ * x * y) ≤
          (Z * x + 2 * D ⟨i, k, hik⟩ * y) ^ 2 := by
      have hextract := DefectPartitionQuadraticExtraction.defect_partition_quadratic_extraction
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone i t k hit htk hik
      have hsignature := RankWeightQuadraticSignature.branden_huh_quadratic_signature
        (DefectPartitionQuadraticExtraction.pairedMatroid M₁ M₂)
        (DefectPartitionQuadraticExtraction.paired_matroid_full_ground M₁ M₂ hfull)
        q hq hqone (DefectPartitionQuadraticExtraction.selectedTripleQuadratic M₁ M₂ q i t k)
        (DefectPartitionQuadraticExtraction.selected_triple_descendant M₁ M₂ q hq i t k)
        hextract.1
      rw [hextract.2] at hsignature
      exact ThreePairSignatureSchur.three_pair_signature_schur
        (D ⟨t, i, hit.symm⟩) (D ⟨i, t, hit⟩) (D ⟨t, k, htk⟩)
        (D ⟨i, k, hik⟩) Z (hD _) hsignature
    exact three_pair_schur_bound
      (D ⟨t, i, hit.symm⟩) (D ⟨i, t, hit⟩) (D ⟨t, k, htk⟩)
      (D ⟨i, k, hik⟩) Z (hD _).le (hD _) (hD _) hZ hschur

end CountingMatroid.Analysis.DefectPartitionTriangle

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · connected the parent to the concrete Tutte-polynomial derivative/substitution construction; proved its homogeneous degree and the real-signature-to-rational-Schur implication. The two remaining prerequisites are the operational Hessian coefficient identity and the explicitly cited Bränden–Huh quadratic signature theorem.
* 2026-10-09 · partial · proved the q=1 branch, positivity of all needed operational totals, and `three_pair_schur_bound`; the sole remaining local gap is the explicit extracted-Hessian Schur-complement bound for 0<q<1. Direct finite-sum positivity does not compare the products; pinned Mathlib and Arlib contain no Lorentzian rank-weight signature or closure theorem.
-/
