import CountingMatroid.Analysis.ConditionalDefectCoefficients
import CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
import CountingMatroid.Analysis.TwoPairSignatureBound
import CountingMatroid.Analysis.DefectPartitionTriangle

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
Bränden–Huh signature declaration. The remaining local gap identifies
coefficients of `conditionedPairPolynomial` with conditional operational
transversal and defect sums. No signature or operational identity is assumed
as an extra theorem hypothesis.
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
  -- This is the sole remaining operational coefficient boundary. All
  -- ordinary-pair extractions and retained-coordinate substitutions below
  -- are evaluated by proved coefficient-calculus lemmas, not by this gap.
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
    dsimp only [P]
    simp_rw [conditioned_pair_tutte_coefficient_sum]
    -- BLOCKER (main.tex:354-367,403-407): the coefficient calculations now
    -- expose a finite sum of coefficients of the original Tutte polynomial.
    -- Reindex its surviving exponent vectors by respecting paired n-sets:
    -- their selected-label exponents must have exactly the occupancy encoded
    -- by the requested exponent, with normalization q^n already checked.
    -- Rewrite the resulting matroid rank weights using
    -- PairedRankValue.paired_rank_eq_eRk and the transversal projection
    -- identity to recover D and Z. No current local lemma carries out this
    -- reindexing and operational coefficient identification.
    -- The root extraction theorem has no σ, and omitted_polynomial sums
    -- use complementary exponents: neither rewrites this expression.
    -- A direct coeff_pderiv rewrite fails at the outer pair identification;
    -- the proved masked-substitution coefficient sum resolves that boundary.
    -- Derivatives at assigned labels and the n! cancellation are now proved
    -- as well. The remaining finite support-to-state sum identity is not a
    -- signature premise and cannot be discharged by positivity.
    sorry
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

* 2026-10-09 · partial · found and used the existing arbitrary-assignment descendants; proved ordinary-pair extraction, coordinate restriction, masked pair identification, selected-label derivative coefficients and the exact n! normalization in ConditionalDefectExtractionCoefficients. Connected both signature-to-inequality arguments. The single remaining gap is reindexing the surviving Tutte coefficient sum as the respecting operational state totals.
* 2026-10-09 · partial · found and used the existing arbitrary-assignment descendants; proved exact ordinary-pair and retained-coordinate coefficient extraction in ConditionalDefectExtractionCoefficients. Connected both signature-to-inequality arguments. The single remaining gap is the selected-label Tutte coefficient identity before ordinary-pair extraction.
* 2026-10-09 · blocked · searched the project and pinned libraries for the conditioned extraction at main.tex:403-417; only the root selected-triple extraction and unsigned omitted-polynomial coefficient sums exist. A Lean root-triangle application fails on the arbitrary-assignment type mismatch. Checked numerical witnesses showing positivity alone implies neither inequality; left the existing target gap in place without new proof debt or assumptions.
-/
