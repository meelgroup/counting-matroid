import CountingMatroid.Analysis.RankWeightQuadraticSignature
import CountingMatroid.Analysis.ThreePairSignatureSchur
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.GreedyRankCorrect
import CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

import CountingMatroid.Analysis.DefectPartitionQuadraticConstruction
import CountingMatroid.Analysis.PairedRankValue
import CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
import CountingMatroid.Analysis.OmittedTutteNormalization
import CountingMatroid.Analysis.ConditionalOperationalCoefficients

set_option autoImplicit false

/-!
The selected triple quadratic has the paper's exact operational Hessian.
Construction provides homogeneity and the vanishing last diagonal entry.
The remaining entries follow from the empty-assignment instance of the
proved conditioned operational coefficient identities, with the ordinary
pair extractions and final derivative multiplicity computed explicitly.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients

/-- INTERNAL: Compute the selected triple coefficient before the operational
occupancy conversion, including the final derivative multiplicity.
TEXLINE: main.tex:412-417 -/
theorem selected_triple_coefficient {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (q : ℚ)
    (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (d : Fin 3 →₀ ℕ) :
    (selectedTripleQuadratic M₁ M₂ q i j k).coeff d =
      (q ^ n / (n.factorial : ℚ)) *
        (linearSubstitution pairSubstitution
          ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))).coeff
          (d.mapDomain (![i, j, k] : Fin 3 → Fin n) + Finsupp.single k 1 +
            ((((List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)).map
              (fun s => Finsupp.single s 1)).sum)) * (d 2 + 1) := by
  classical
  have hf : Function.Injective (![i, j, k] : Fin 3 → Fin n) := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all
  have hweights : tripleSubstitution i j k =
      fun s t => if s = (![i, j, k] : Fin 3 → Fin n) t then 1 else 0 := by
    funext s t
    fin_cases t <;> by_cases hi : s = i <;> by_cases hj : s = j <;>
      by_cases hk : s = k <;> simp_all [tripleSubstitution]
  unfold selectedTripleQuadratic
  rw [MvPolynomial.coeff_C_mul, hweights, restriction_coefficient _ hf,
    MvPolynomial.coeff_pderiv]
  have hkval : (d.mapDomain (![i, j, k] : Fin 3 → Fin n)) k = d 2 := by
    simpa using Finsupp.mapDomain_apply hf d 2
  rw [hkval, extract_list_coefficient _ ((List.nodup_finRange n).filter _)]
  · ring
  · intro s hs
    simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hs
    have hzero : (d.mapDomain (![i, j, k] : Fin 3 → Fin n)) s = 0 := by
      apply Finsupp.mapDomain_of_notMem_range
      rintro ⟨t, ht⟩
      fin_cases t <;> simp_all
    simp [Finsupp.add_apply, hzero, hs.2.2]

/-- PAPER: main.tex:403-417
The selected quadratic is homogeneous of degree two, and its Hessian has
exactly the operational transversal and ordered-defect totals. The n-set
rank weights here must be identified with the paired matroid's ranks using
the two original independence oracles; no additional rank oracle is input. -/
theorem defect_partition_quadratic_extraction (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1)
    (i t k : Fin n) (hit : i ≠ t) (htk : t ≠ k) (hik : i ≠ k) :
    (selectedTripleQuadratic M₁ M₂ q i t k).IsHomogeneous 2 ∧
      hessian (selectedTripleQuadratic M₁ M₂ q i t k) =
        threePairMatrix
          (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨t, i, hit.symm⟩)
          (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, t, hit⟩)
          (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨t, k, htk⟩)
          (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, hik⟩)
          (TransversalPartition.partitionSum r o₁ o₂ q) := by
  classical
  refine ⟨selected_triple_homogeneous M₁ M₂ q i t k hit htk hik, ?_⟩
  ext s u
  by_cases hlast : s = 2 ∧ u = 2
  · rcases hlast with ⟨rfl, rfl⟩
    simpa [threePairMatrix] using selected_triple_last_diagonal_zero M₁ M₂ q i t k
  have hsub : conditionedPairSubstitution (fun _ : Fin n => none) =
      pairSubstitution := by
    funext e v
    cases e <;> simp [conditionedPairSubstitution, pairSubstitution]
  have hsource : conditionedPairPolynomial M₁ M₂ q (fun _ => none) =
      MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
        linearSubstitution pairSubstitution
          ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q)) := by
    simp [conditionedPairPolynomial, assignedPairs, hsub]
  let ordinary := (List.finRange n).filter (fun v => v ≠ i ∧ v ≠ t ∧ v ≠ k)
  have hset : ordinary.toFinset = (Finset.univ : Finset (Fin n)) \ {i, t, k} := by
    ext v
    simp [ordinary]
  have hexp : (ordinary.map (fun v => Finsupp.single v 1)).sum =
      ordinaryExponent (fun _ => none) {i, t, k} := by
    rw [← List.sum_toFinset _ ((List.nodup_finRange n).filter _), hset]
    simp [ordinaryExponent, assignedPairs,
      ← List.sum_toFinset _ (Finset.nodup_toList _)]
  rw [hessian_coefficient, selected_triple_coefficient M₁ M₂ q i t k hit htk hik,
    show ((((List.finRange n).filter (fun v => v ≠ i ∧ v ≠ t ∧ v ≠ k)).map
      (fun v => Finsupp.single v 1)).sum) = ordinaryExponent (fun _ => none) {i, t, k}
      from hexp]
  have hcoeff :=
    (CountingMatroid.Analysis.ConditionalOperationalCoefficients.conditional_operational_coefficients
      n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq (fun _ => none)).2
      i t k hit htk hik rfl rfl rfl s u
  rw [hsource, MvPolynomial.coeff_C_mul] at hcoeff
  simpa only [defect_total_empty, transversal_total_empty] using hcoeff

end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2026-10-09 · proved · closed the triple Hessian extraction using the now-importable proved conditional operational coefficients at the empty assignment; promoted the preserved coefficient calculation to selected_triple_coefficient.

* r2026-10-09 · partially proved · proved and used the last diagonal Hessian entry from two-label squarefreeness; all new support lemmas are closed, while the other entries retain the operational-partition boundary.
* r2026-10-09 · dependency refined · found proved normalization in OmittedTutteNormalization and its additional cycle through OmittedSlotQuadratic; the earlier two-import construction split would leave this cycle intact.
* r2026-10-09 · diagnostic verified · a complete selected-quadratic coefficient calculation checks on stdin using the existing downstream extraction lemmas; retained the proof above the remaining boundary.
* r2026-10-09 · blocked · confirmed extraction-calculus and paired-rank dependencies import this module; recorded the construction split needed to reuse them without duplicating proofs.
-/
