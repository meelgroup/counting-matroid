import CountingMatroid.Analysis.ConditionalDefectCoefficients

set_option autoImplicit false

/-!
The two coefficient inequalities for partial transversal assignments.
The coefficients are the concrete finite operational-rank sums defined in
`ConditionalDefectCoefficients`, rather than unspecified polynomial data.
The remaining step is their selected-element quadratic signature extraction
for arbitrary assignments. `DefectPartitionQuadraticExtraction` constructs
only an unconditioned three-pair quadratic, and `OmittedRankWeightPolynomial`
identifies conditional coefficient sums without a descendant or signature
bound. Neither currently supplies the conditioned extraction required here.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficientBounds

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients

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
  have hz := transversal_total_pos r o₁ o₂ q hq σ
  have hc (index : DefectIndex n) (he : σ index.emptyPair = none)
      (hf : σ index.fullPair = none) := defect_total_pos r o₁ o₂ q hq σ index he hf
  -- Concrete extraction route: the two-pair quadratic has entries
  -- (2*c_ji,z;z,2*c_ij). The triple quadratic has A_jj=2*c_ij,
  -- A_ik=2*c_jk, A_ij=z, A_jk=2*c_ik. Positivity above supplies
  -- the positive pivot. It does not establish the signature premise.
  /- Retained root-specialization probe from this attempt. It is not used
  by the universal proof, so its diagnostic import was removed to avoid
  making this independent child wait on the active root-triangle owner.
  -- The root triple specialization already belongs to another owner:
  have hrootTriple (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
      defectTotal r o₁ o₂ q (fun _ => none) ⟨i, j, hij⟩ *
        defectTotal r o₁ o₂ q (fun _ => none) ⟨j, k, hjk⟩ ≤
          transversalTotal r o₁ o₂ q (fun _ => none) *
            defectTotal r o₁ o₂ q (fun _ => none) ⟨i, k, hik⟩ := by
    simpa only [defect_total_empty, transversal_total_empty] using
      DefectPartitionTriangle.defect_partition_triangle n r M₁ M₂ o₁ o₂ q
        hfull hr h₁ h₂ hq hqone i j k hij hjk hik
  -/
  -- STILL OPEN: identify the operational paired-rank polynomial with F,
  -- implement derivative/zero/identification extraction, and obtain these
  -- Hessian signature bounds. The cited input is BH2020, Theorems 4.10,
  -- 2.10 and Corollary 2.11 (main.tex:334-347); the extraction itself is
  -- proved by the paper and must not be proposed as a Prior field.
  -- BLOCKER (main.tex:403-417): no local declaration constructs the pair
  -- and triple quadratics after differentiating the selected labels of σ
  -- and deleting both variables of every assigned pair, and identifies
  -- their Hessians with the displayed conditional operational totals.
  -- `selectedTripleQuadratic` and `defect_partition_quadratic_extraction`
  -- have no assignment parameter: they identify root partition sums only.
  -- Applying `defect_partition_triangle` with `simpa only
  -- [defect_total_empty, transversal_total_empty]` to the σ goal produces
  -- a type mismatch between those root sums and the conditional totals.
  -- `defect_coefficient_sum` supplies only a sum of coefficients of the
  -- omitted polynomial, with neither a Tutte descendant nor a Hessian.
  -- The general `branden_huh_quadratic_signature` can supply the signature
  -- once the conditioned descendant and homogeneous-degree/entry identities
  -- exist; its statement alone cannot identify these operational totals.
  sorry

end CountingMatroid.Analysis.ConditionalDefectCoefficientBounds

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · blocked · searched the project and pinned libraries for the conditioned extraction at main.tex:403-417; only the root selected-triple extraction and unsigned omitted-polynomial coefficient sums exist. A Lean root-triangle application fails on the arbitrary-assignment type mismatch. Checked numerical witnesses showing positivity alone implies neither inequality; left the existing target gap in place without new proof debt or assumptions.
-/
