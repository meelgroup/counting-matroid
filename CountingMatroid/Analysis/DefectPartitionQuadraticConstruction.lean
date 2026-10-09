import CountingMatroid.Analysis.RankWeightQuadraticSignature
import CountingMatroid.Analysis.ThreePairSignatureSchur
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.GreedyRankCorrect
import CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
import Mathlib.Combinatorics.Matroid.Sum
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

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

/-- INTERNAL: Differentiating a merged pair sums the two label derivatives.
TEXLINE: main.tex:403-407 -/
theorem pair_substitution_derivative {n : ℕ} (j : Fin n)
    (p : MvPolynomial (Option (PairedGround n)) ℚ) :
    MvPolynomial.pderiv j (linearSubstitution pairSubstitution p) =
      linearSubstitution pairSubstitution
        (MvPolynomial.pderiv (some (j, false)) p +
          MvPolynomial.pderiv (some (j, true)) p) := by
  classical
  unfold linearSubstitution
  rw [CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv]
  congr 1
  simp [pairSubstitution, Fintype.sum_prod_type, Finset.sum_add_distrib, add_comm]

/-- INTERNAL: Extraction at an ordinary pair commutes with differentiation
at a distinct retained pair.
TEXLINE: main.tex:408-417 -/
theorem extract_one_derivative_commute {n : ℕ} (j k : Fin n) (hjk : j ≠ k)
    (p : MvPolynomial (Fin n) ℚ) :
    MvPolynomial.pderiv k (extractOne j p) = extractOne j (MvPolynomial.pderiv k p) := by
  classical
  unfold extractOne
  rw [linear_substitution_derivative_single _ k k]
  · rw [derivative_commute k j]
  · intro s
    by_cases hs : s = j
    · subst s; simp [hjk]
    · simp [hs]

/-- INTERNAL: The last diagonal Hessian entry vanishes: the merged pair k
has at most two selected labels, and this entry takes three k derivatives.
TEXLINE: main.tex:412-417 -/
theorem selected_triple_last_diagonal_zero {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (i j k : Fin n) :
    hessian (selectedTripleQuadratic M₁ M₂ q i j k) 2 2 = 0 := by
  classical
  let f := linearSubstitution pairSubstitution
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))
  let ordinary := (List.finRange n).filter (fun s => s ≠ i ∧ s ≠ j ∧ s ≠ k)
  let cubic := ordinary.foldl (fun g s => extractOne s g) f
  have hf : MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k f)) = 0 := by
    dsimp only [f]
    rw [pair_substitution_derivative, pair_substitution_derivative, pair_substitution_derivative]
    have hnil := tutte_two_label_derivative_cube (pairedMatroid M₁ M₂) q
      (k, false) (k, true) n
    dsimp only at hnil
    rw [hnil]
    simp [linearSubstitution]
  have hfold (l : List (Fin n)) (hl : ∀ s ∈ l, s ≠ k)
      (g : MvPolynomial (Fin n) ℚ)
      (hg : MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k g)) = 0) :
      MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k
        (l.foldl (fun p s => extractOne s p) g))) = 0 := by
    induction l generalizing g with
    | nil => exact hg
    | cons s l ih =>
      apply ih (fun t ht => hl t (by simp [ht]))
      rw [extract_one_derivative_commute s k (hl s (by simp)),
        extract_one_derivative_commute s k (hl s (by simp)),
        extract_one_derivative_commute s k (hl s (by simp)), hg]
      simp [extractOne, linearSubstitution]
  have hc : MvPolynomial.pderiv k (MvPolynomial.pderiv k (MvPolynomial.pderiv k cubic)) = 0 :=
    hfold ordinary (by
      intro s hs
      simp only [ordinary, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq] at hs
      exact hs.2.2) f hf
  have hcolumn : ∀ s, tripleSubstitution i j k s 2 = if s = k then 1 else 0 := by
    intro s
    simp [tripleSubstitution, show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide]
  have hrestrict := linear_substitution_derivative_single
    (tripleSubstitution i j k) k (2 : Fin 3) hcolumn
  change ((MvPolynomial.constantCoeff
    (MvPolynomial.pderiv 2 (MvPolynomial.pderiv 2
      (MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
        linearSubstitution (tripleSubstitution i j k) (MvPolynomial.pderiv k cubic)))) : ℚ) : ℝ) = 0
  simp only [MvPolynomial.pderiv_C_mul]
  rw [hrestrict, hrestrict, hc]
  simp [linearSubstitution]

end CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
