import CountingMatroid.Analysis.ConditionalDefectCoefficients
import CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
import CountingMatroid.Analysis.TwoPairSignatureBound
import CountingMatroid.Analysis.DefectPartitionTriangle
import CountingMatroid.Analysis.ConditionalOperationalCoefficients

set_option autoImplicit false

/-!
The two coefficient inequalities for partial transversal assignments.
The coefficients are the concrete finite operational-rank sums defined in
`ConditionalDefectCoefficients`, rather than unspecified polynomial data.
The actual conditioned descendants and their degrees are constructed in
`ConditionalDefectQuadratics`. Their exact ordinary-pair extraction and
coordinate-restriction coefficient calculations, selected-label derivatives,
and exact q^n/n! normalization are proved in
`ConditionalDefectExtractionCoefficients` and used below. The determinant
and Schur consequences are connected to those descendants via the existing
Bränden–Huh signature declaration. The exact normalization and operational
rank-weight state sums are proved in `ConditionalSelectedStateSum`.
`ConditionalOperationalCoefficients` carries the remaining independent
occupancy-to-classification identity used here. The target has no local
proof gap; completion depends on that coefficient bridge and the existing
signature input. No extra theorem hypothesis is introduced.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open CountingMatroid.Analysis.TwoPairSignatureBound
open CountingMatroid.Analysis.ThreePairSignatureSchur

/-- PAPER: main.tex:397-449
Both defect inequalities hold at every conditioning node, with all displayed
defect indices unassigned and pairwise distinct. -/
theorem conditional_defect_coefficient_bounds (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (σ : Assignment n) :
    (∀ (i j : Fin n) (hij : i ≠ j), σ i = none → σ j = none →
      4 * defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩ *
        defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩ ≤
          transversalTotal r o₁ o₂ q σ ^ 2) ∧
    (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
      σ i = none → σ j = none → σ k = none →
      defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩ *
        defectTotal r o₁ o₂ q σ ⟨j, k, hjk⟩ ≤
          transversalTotal r o₁ o₂ q σ * defectTotal r o₁ o₂ q σ ⟨i, k, hik⟩) := by
  classical
  let P := conditionedPairPolynomial M₁ M₂ q σ
  let D := defectTotal r o₁ o₂ q σ
  let Z := transversalTotal r o₁ o₂ q σ
  have hz : 0 < Z := transversal_total_pos r o₁ o₂ q hq σ
  have hc (index : DefectIndex n) (he : σ index.emptyPair = none)
      (hf : σ index.fullPair = none) : 0 < D index :=
    defect_total_pos r o₁ o₂ q hq σ index he hf
  -- The coefficient bridge uses the proved operational state-sum
  -- representation; the determinant and Schur arguments below use its
  -- exact pair and triple entries.
  have hcoeff :
      (∀ (i j : Fin n) (hij : i ≠ j), σ i = none → σ j = none →
        ∀ s t : Fin 2,
          ((P.coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j] : Fin 2 → Fin n) + ordinaryExponent σ {i, j}) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          twoPairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩) Z s t) ∧
      (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
        σ i = none → σ j = none → σ k = none → ∀ s t : Fin 3,
          ((P.coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j, k] : Fin 3 → Fin n) + Finsupp.single k 1 +
              ordinaryExponent σ {i, j, k}) *
            ((Finsupp.single s 1 + Finsupp.single t 1 : Fin 3 →₀ ℕ) 2 + 1) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          threePairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩)
            (D ⟨j, k, hjk⟩) (D ⟨i, k, hik⟩) Z s t) := by
    exact CountingMatroid.Analysis.ConditionalOperationalCoefficients.conditional_operational_coefficients
      n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ

  constructor
  · intro i j hij hi hj
    have hquad := conditioned_pair_quadratic M₁ M₂ q hq σ i j hij hi hj
    have hsig := branden_huh_quadratic_signature (pairedMatroid M₁ M₂)
      (paired_matroid_full_ground M₁ M₂ hfull) q hq hqone
      (conditionedPairQuadratic M₁ M₂ q σ i j) hquad.1 hquad.2
    have hmatrix : hessian (conditionedPairQuadratic M₁ M₂ q σ i j) =
        twoPairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩) Z := by
      ext s t
      rw [hessian_coefficient, conditioned_pair_coefficient M₁ M₂ q σ i j hij]
      exact hcoeff.1 i j hij hi hj s t
    rw [hmatrix] at hsig
    exact two_pair_signature_bound _ _ _ (hc _ hj hi) hsig
  · intro i j k hij hjk hik hi hj hk
    have hquad := conditioned_triple_quadratic M₁ M₂ q hq σ i j k hij hjk hik hi hj hk
    have hsig := branden_huh_quadratic_signature (pairedMatroid M₁ M₂)
      (paired_matroid_full_ground M₁ M₂ hfull) q hq hqone
      (conditionedTripleQuadratic M₁ M₂ q σ i j k) hquad.1 hquad.2
    have hmatrix : hessian (conditionedTripleQuadratic M₁ M₂ q σ i j k) =
        threePairMatrix (D ⟨j, i, hij.symm⟩) (D ⟨i, j, hij⟩)
          (D ⟨j, k, hjk⟩) (D ⟨i, k, hik⟩) Z := by
      ext s t
      rw [hessian_coefficient,
        conditioned_triple_coefficient M₁ M₂ q σ i j k hij hjk hik]
      exact hcoeff.2 i j k hij hjk hik hi hj hk s t
    rw [hmatrix] at hsig
    have hschur := three_pair_signature_schur _ _ _ _ _ (hc _ hi hj) hsig
    exact CountingMatroid.Analysis.DefectPartitionTriangle.three_pair_schur_bound
      _ _ _ _ _ (hc _ hj hi).le (hc _ hi hj) (hc _ hi hk) hz hschur

end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · proved arbitrary-assignment selected-state normalization, monomial conditioning, assignment equivalence and operational coefficient sums in ConditionalSelectedStateSum. The parent now uses ConditionalOperationalCoefficients for the remaining finite occupancy-to-classification reindexing; both downstream signature arguments are unchanged.
* 2026-10-09 · partial · found and used the existing arbitrary-assignment descendants; proved ordinary-pair extraction, coordinate restriction, masked pair identification, selected-label derivative coefficients and the exact n! normalization in ConditionalDefectExtractionCoefficients. Connected both signature-to-inequality arguments. The single remaining gap is reindexing the surviving Tutte coefficient sum as the respecting operational state totals.
* 2026-10-09 · partial · found and used the existing arbitrary-assignment descendants; proved exact ordinary-pair and retained-coordinate coefficient extraction in ConditionalDefectExtractionCoefficients. Connected both signature-to-inequality arguments. The single remaining gap is the selected-label Tutte coefficient identity before ordinary-pair extraction.
* 2026-10-09 · blocked · searched the project and pinned libraries for the conditioned extraction at main.tex:403-417; only the root selected-triple extraction and unsigned omitted-polynomial coefficient sums exist. A Lean root-triangle application fails on the arbitrary-assignment type mismatch. Checked numerical witnesses showing positivity alone implies neither inequality; left the existing target gap in place without new proof debt or assumptions.
-/
