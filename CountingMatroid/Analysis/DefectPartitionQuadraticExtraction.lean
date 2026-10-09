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

set_option autoImplicit false

/-!
The concrete selected-element quadratic used in the three-pair inequality.
It is constructed from the homogenized Tutte polynomial by the paper's
actual derivative and substitution sequence. Its membership in the allowed
closure operations is proved separately from its operational coefficients.
Its last diagonal Hessian entry is proved to vanish directly from squarefree
label exponents, without any operational coefficient identity.
The remaining coefficient identities need the paired-rank correspondence
and extraction calculation; it does not assume a signature theorem. The
existing paired-rank correspondence and extraction-calculus lemmas live in
modules that import this module. Reusing them here requires separating the
construction declarations above the operational extraction theorem from
that theorem, so those dependencies no longer import their consumer.
-/

namespace CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ThreePairSignatureSchur
open CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

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
  rw [hessian_coefficient]
  -- This is now a coefficient calculation, with the repeated-variable
  -- multiplicity handled by the proved `hessian_coefficient` identity.
  -- BLOCKER (dependency cycle, main.tex:354-367,403-417): the existing
  -- ConditionalDefectExtractionCoefficients.extract_list_coefficient and
  -- ConditionalDefectExtractionCoefficients.restriction_coefficient compute
  -- the ordinary-pair extraction and retained-coordinate substitution, but
  -- their module imports ConditionalDefectQuadratics, which imports this
  -- module. PairedRankValue.paired_rank_eq_eRk supplies the exact required
  -- operational rank identity, but PairedRankValue also imports this module.
  -- Neither dependency may be imported here without a cycle, and reproducing
  -- these already-proved declarations would duplicate the existing proofs.
  -- Separate the construction declarations above into a construction module
  -- (preserving their fully qualified names), then make PairedRankValue and
  -- ConditionalDefectQuadratics import that construction module. This module
  -- can then import PairedRankValue and ConditionalDefectExtractionCoefficients.
  -- OmittedTutteNormalization.normalized_tutte_polynomial already proves
  -- the normalized homogenizer slice, but is also downstream via both
  -- ConditionalDefectExtractionCoefficients and PairedRankValue.
  -- Its additional import through OmittedSlotQuadratic must be redirected
  -- to the construction module as well before normalization is importable.
  -- After that structural repair, use the proved normalization and rank
  -- identities, then group their n-element monomials by pair occupancy.
  -- Precisely, put P = C(q^n/n!) * linearSubstitution pairSubstitution
  -- ((pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q)).
  -- The remaining operational bridges are
  --   P.coeff (∑ s : Fin n, Finsupp.single s 1) = partitionSum r o₁ o₂ q
  -- and, for every ordered index a,
  --   P.coeff (Finsupp.single a.fullPair 2 +
  --     ∑ s ∈ Finset.univ \ {a.emptyPair, a.fullPair}, Finsupp.single s 1)
  --     = defectPartition r o₁ o₂ q a.
  -- The first occupancy selects exactly one label in each pair. The second
  -- selects no label in a.emptyPair, both labels in a.fullPair, and exactly
  -- one in every other pair. Identify them with transversalState and
  -- classify_defect_iff. The final k derivative has multiplicity d 2 + 1;
  -- hessian_coefficient supplies the diagonal multiplicity separately.
  -- Positivity or a signature theorem cannot discharge this equality.
  /- Verified diagnostic (lake env lean --stdin, 2026-10-09): this proof
  checks when the two downstream modules are imported. It is retained here
  as evidence for the structural refactor, rather than duplicating their
  extraction lemmas or creating another open proof obligation.

  example {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (q : ℚ)
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
  -/
  sorry

end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2026-10-09 · partially proved · proved and used the last diagonal Hessian entry from two-label squarefreeness; all new support lemmas are closed, while the other entries retain the operational-partition boundary.
* r2026-10-09 · dependency refined · found proved normalization in OmittedTutteNormalization and its additional cycle through OmittedSlotQuadratic; the earlier two-import construction split would leave this cycle intact.
* r2026-10-09 · diagnostic verified · a complete selected-quadratic coefficient calculation checks on stdin using the existing downstream extraction lemmas; retained the proof above the remaining boundary.
* r2026-10-09 · blocked · confirmed extraction-calculus and paired-rank dependencies import this module; recorded the construction split needed to reuse them without duplicating proofs.
-/
