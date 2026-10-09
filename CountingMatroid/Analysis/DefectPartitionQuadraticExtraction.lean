import CountingMatroid.Analysis.RankWeightQuadraticSignature
import CountingMatroid.Analysis.ThreePairSignatureSchur
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.GreedyRankCorrect
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

set_option autoImplicit false

/-!
The concrete selected-element quadratic used in the three-pair inequality.
It is constructed from the homogenized Tutte polynomial by the paper's
actual derivative and substitution sequence. Its membership in the allowed
closure operations is proved separately from its operational coefficients.
The remaining coefficient identity needs the paired-rank correspondence
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

/-- PAPER: main.tex:262-272
The direct sum of the first matroid and the second matroid's dual, on the
existing paired labels; false denotes x and true denotes y. -/
noncomputable def pairedMatroid {n : ℕ} (M₁ M₂ : Matroid (Fin n)) :
    Matroid (PairedGround n) :=
  (Matroid.sum' (fun b : Bool => if b then M₂✶ else M₁)).mapEquiv
    (Equiv.prodComm Bool (Fin n))

/-- INTERNAL: The paired matroid has exactly the supplied paired ground.
TEXLINE: main.tex:262-272 -/
theorem paired_matroid_full_ground {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hfull : FullGround M₁ M₂) : (pairedMatroid M₁ M₂).E = Set.univ := by
  ext e
  rcases e with ⟨i, b⟩
  cases b <;> simp [pairedMatroid, hfull.1, hfull.2]

/-- INTERNAL: Identify the two label variables of a pair and set the
homogenizing variable to zero.
TEXLINE: main.tex:354-373,403-407 -/
noncomputable def pairSubstitution {n : ℕ} : Option (PairedGround n) → Fin n → ℚ
  | none, _ => 0
  | some e, j => if e.1 = j then 1 else 0

/-- INTERNAL: Delete a variable after differentiating, extracting precisely
exponent one rather than all positive exponents.
TEXLINE: main.tex:369-373 -/
noncomputable def extractOne {n : ℕ} (j : Fin n)
    (g : MvPolynomial (Fin n) ℚ) : MvPolynomial (Fin n) ℚ :=
  linearSubstitution (fun s t => if s = j then 0 else if s = t then 1 else 0)
    (MvPolynomial.pderiv j g)

/-- INTERNAL: Retain the three distinguished pair variables, in the order
i,j,k, and delete the already extracted ordinary-pair variables.
TEXLINE: main.tex:412-417 -/
noncomputable def tripleSubstitution {n : ℕ} (i j k : Fin n) :
    Fin n → Fin 3 → ℚ := fun s t =>
  if s = i ∧ t = 0 then 1 else
    if s = j ∧ t = 1 then 1 else if s = k ∧ t = 2 then 1 else 0

/-- INTERNAL: The specific quadratic obtained by the paper's extraction
from T: n homogenizing derivatives, z₀=0 and pair identification, extraction
of all ordinary pairs, and one derivative at k, scaled by qⁿ/n!.
TEXLINE: main.tex:354-373,403-417 -/
noncomputable def selectedTripleQuadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (i j k : Fin n) : MvPolynomial (Fin 3) ℚ :=
  let f := linearSubstitution pairSubstitution
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))
  let ordinary := (List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)
  let cubic := ordinary.foldl (fun g s => extractOne s g) f
  MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
    linearSubstitution (tripleSubstitution i j k) (MvPolynomial.pderiv k cubic)

/-- INTERNAL: The selected quadratic is a descendant under exactly the
closure operations of the Bränden–Huh input, with no coefficient identity
or signature assumption used in this construction.
TEXLINE: main.tex:354-373,403-417 -/
theorem selected_triple_descendant {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (hq : 0 < q) (i j k : Fin n) :
    Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin 3)
      (selectedTripleQuadratic M₁ M₂ q i j k) := by
  classical
  let T := tuttePolynomial (pairedMatroid M₁ M₂) q
  have hiter (m : ℕ) : Descendant T (Option (PairedGround n))
      ((MvPolynomial.pderiv none)^[m] T) := by
    induction m with
    | zero => exact Descendant.initial
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Descendant.derivative none ih
  have hf : Descendant T (Fin n)
      (linearSubstitution pairSubstitution ((MvPolynomial.pderiv none)^[n] T)) := by
    apply Descendant.substitute _ _ (hiter n)
    intro s t
    cases s <;> simp [pairSubstitution]
    split_ifs <;> norm_num
  have hfold (l : List (Fin n)) (g : MvPolynomial (Fin n) ℚ)
      (hg : Descendant T (Fin n) g) :
      Descendant T (Fin n) (l.foldl (fun p s => extractOne s p) g) := by
    induction l generalizing g with
    | nil => exact hg
    | cons s l ih =>
      apply ih
      apply Descendant.substitute _ _ (Descendant.derivative s hg)
      intro u v
      split_ifs <;> norm_num
  apply Descendant.scale _ (by positivity)
  apply Descendant.substitute _ _ (Descendant.derivative k (hfold _ _ hf))
  intro s t
  unfold tripleSubstitution
  split_ifs <;> norm_num

/-- INTERNAL: Every monomial in the homogenized Tutte sum has degree equal
to the cardinality of the ground type.
TEXLINE: main.tex:334-339 -/
theorem tutte_polynomial_homogeneous {α : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) :
    (tuttePolynomial N q).IsHomogeneous (Fintype.card α) := by
  classical
  unfold tuttePolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro A hA
  have hprod : (∏ a ∈ A, (MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ)).IsHomogeneous
      A.card := by
    simpa using MvPolynomial.IsHomogeneous.prod A
      (fun a => (MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ))
      (fun _ => 1) (fun a _ => MvPolynomial.isHomogeneous_X ℚ (some a))
  have hdegree : Fintype.card α - A.card + A.card = Fintype.card α :=
    Nat.sub_add_cancel (Finset.card_le_univ A)
  rw [mul_assoc]
  simpa only [hdegree] using
    ((MvPolynomial.isHomogeneous_X_pow none (Fintype.card α - A.card)).mul hprod).C_mul
      ((q ^ (N.eRk (A : Set α)).toNat)⁻¹)

/-- INTERNAL: A homogeneous linear substitution preserves the degree,
including substitution by zero.
TEXLINE: main.tex:340-343 -/
theorem linear_substitution_homogeneous {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (g : MvPolynomial σ ℚ) (m : ℕ)
    (hg : g.IsHomogeneous m) : (linearSubstitution a g).IsHomogeneous m := by
  unfold linearSubstitution
  simpa only [one_mul] using hg.aeval
    (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t)
    (fun s => MvPolynomial.IsHomogeneous.sum _ _ 1
      (fun t _ => MvPolynomial.isHomogeneous_C_mul_X (a s t) t))

/-- INTERNAL: Counting the ordinary-pair extractions shows that the selected
polynomial is homogeneous quadratic, independently of its rank coefficients.
TEXLINE: main.tex:412-417 -/
theorem selected_triple_homogeneous {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    (selectedTripleQuadratic M₁ M₂ q i j k).IsHomogeneous 2 := by
  classical
  let T := tuttePolynomial (pairedMatroid M₁ M₂) q
  have hT : T.IsHomogeneous (2 * n) := by
    simpa [T, PairedGround, Nat.mul_comm] using
      tutte_polynomial_homogeneous (pairedMatroid M₁ M₂) q
  have hiter (m : ℕ) : ((MvPolynomial.pderiv none)^[m] T).IsHomogeneous (2 * n - m) := by
    induction m with
    | zero => simpa using hT
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.sub_sub] using ih.pderiv (i := none)
  have hf : (linearSubstitution pairSubstitution
      ((MvPolynomial.pderiv none)^[n] T)).IsHomogeneous n := by
    have hn : 2 * n - n = n := by omega
    simpa only [hn] using linear_substitution_homogeneous pairSubstitution _ _ (hiter n)
  let ordinary := (List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)
  have hcard : ordinary.length = n - 3 := by
    have hfinset : ordinary.toFinset = (Finset.univ : Finset (Fin n)) \ {i, j, k} := by
      ext s
      simp [ordinary]
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), hfinset]
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
    simp [hij, hjk, hik]
  have hn : 3 ≤ n := by
    have hle := Finset.card_le_univ ({i, j, k} : Finset (Fin n))
    simpa [hij, hjk, hik] using hle
  have hfold (l : List (Fin n)) (g : MvPolynomial (Fin n) ℚ) (d : ℕ)
      (hg : g.IsHomogeneous d) :
      (l.foldl (fun p s => extractOne s p) g).IsHomogeneous (d - l.length) := by
    induction l generalizing g d with
    | nil => simpa using hg
    | cons s l ih =>
      have hs := linear_substitution_homogeneous
        (fun u v : Fin n => if u = s then 0 else if u = v then 1 else 0)
        _ _ (hg.pderiv (i := s))
      simpa [extractOne, Nat.sub_sub, Nat.add_comm] using ih (extractOne s g) (d - 1) hs
  have hcubic := hfold ordinary _ n hf
  rw [hcard, show n - (n - 3) = 3 by omega] at hcubic
  have hquad := linear_substitution_homogeneous (tripleSubstitution i j k) _ _
    (hcubic.pderiv (i := k))
  exact hquad.C_mul _

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
  -- After that structural repair, the mathematical work still needed is the
  -- normalized Tutte-sum coefficient identity: the homogenizing derivative
  -- and deletion retain exactly the n-element paired subsets, each weighted
  -- by q^(n-rank). Group their monomials by pair occupancy, identify defect
  -- occupancy with classify_defect_iff, and identify transversal occupancy
  -- with transversalState. The final k derivative has multiplicity d 2 + 1;
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

* r2026-10-09 · diagnostic verified · a complete selected-quadratic coefficient calculation checks on stdin using the existing downstream extraction lemmas; retained the proof above the remaining boundary.
* r2026-10-09 · blocked · confirmed extraction-calculus and paired-rank dependencies import this module; recorded the construction split needed to reuse them without duplicating proofs.
-/
