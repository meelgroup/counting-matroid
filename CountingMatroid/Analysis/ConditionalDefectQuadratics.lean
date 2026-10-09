import CountingMatroid.Analysis.DefectPartitionQuadraticConstruction
import CountingMatroid.Analysis.ConditionalDefectCoefficients

set_option autoImplicit false

/-!
Concrete selected-element descendants for an arbitrary partial assignment.
Differentiation fixes the selected label at each assigned pair; substitution
deletes both labels of those pairs and identifies each remaining pair.
Ordinary-pair extraction then leaves the distinguished pair variables.
The descendant and homogeneous-degree facts below do not assert identities
between polynomial coefficients and operational rank sums.
-/

namespace CountingMatroid.Analysis.ConditionalDefectQuadratics

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

/-- INTERNAL: The pair indices at which a partial assignment selects a label.
TEXLINE: main.tex:403-407 -/
noncomputable def assignedPairs {n : ℕ} (σ : Assignment n) : Finset (Fin n) :=
  Finset.univ.filter (fun i => σ i ≠ none)

/-- INTERNAL: Delete both variables of assigned pairs, and identify the two
variables in each unassigned pair, also deleting the homogenizing variable.
TEXLINE: main.tex:403-407 -/
noncomputable def conditionedPairSubstitution {n : ℕ} (σ : Assignment n) :
    Option (PairedGround n) → Fin n → ℚ
  | none, _ => 0
  | some e, j => if σ e.1 = none ∧ e.1 = j then 1 else 0

/-- INTERNAL: The paper's conditioned selected-element polynomial, before
ordinary-pair extraction, constructed from the matroid Tutte polynomial.
TEXLINE: main.tex:354-367,403-407 -/
noncomputable def conditionedPairPolynomial {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) : MvPolynomial (Fin n) ℚ :=
  MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
    linearSubstitution (conditionedPairSubstitution σ)
      ((assignedPairs σ).toList.foldl
        (fun g i => MvPolynomial.pderiv (some (i, (σ i).getD false)) g)
        ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q)))

/-- INTERNAL: Extract exactly one selected element at every unassigned pair
outside the retained set of distinguished indices.
TEXLINE: main.tex:408-417 -/
noncomputable def retainedPolynomial {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (retained : Finset (Fin n)) :
    MvPolynomial (Fin n) ℚ :=
  ((Finset.univ \ (assignedPairs σ ∪ retained)).toList).foldl
    (fun g i => extractOne i g) (conditionedPairPolynomial M₁ M₂ q σ)

/-- INTERNAL: Iterating selected-label derivatives preserves descendant status.
TEXLINE: main.tex:403-407 -/
private theorem derivative_fold_descendant {α β : Type}
    (T : MvPolynomial α ℚ) (l : List β) (label : β → α)
    (g : MvPolynomial α ℚ) (hg : Descendant T α g) :
    Descendant T α (l.foldl (fun p i => MvPolynomial.pderiv (label i) p) g) := by
  induction l generalizing g with
  | nil => exact hg
  | cons i l ih => exact ih _ (Descendant.derivative (label i) hg)

/-- INTERNAL: Iterating selected-label derivatives subtracts their count
from homogeneous degree, including zero polynomials at boundary degrees.
TEXLINE: main.tex:403-407 -/
private theorem derivative_fold_homogeneous {α β : Type}
    (l : List β) (label : β → α) (g : MvPolynomial α ℚ) (d : ℕ)
    (hg : g.IsHomogeneous d) :
    (l.foldl (fun p i => MvPolynomial.pderiv (label i) p) g).IsHomogeneous
      (d - l.length) := by
  induction l generalizing g d with
  | nil => simpa using hg
  | cons i l ih =>
    simpa [Nat.sub_sub, Nat.add_comm] using ih _ (d - 1) (hg.pderiv (i := label i))

/-- INTERNAL: The conditioned polynomial follows only the closure operations
allowed by the Bränden–Huh signature input.
TEXLINE: main.tex:354-367,403-407 -/
theorem conditioned_pair_descendant {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) :
    Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin n)
      (conditionedPairPolynomial M₁ M₂ q σ) := by
  have hiter (m : ℕ) :
      Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Option (PairedGround n))
        ((MvPolynomial.pderiv none)^[m] (tuttePolynomial (pairedMatroid M₁ M₂) q)) := by
    induction m with
    | zero => exact Descendant.initial
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Descendant.derivative none ih
  apply Descendant.scale _ (by positivity)
  apply Descendant.substitute _ _ (derivative_fold_descendant _ _ _ _ (hiter n))
  intro s t
  cases s <;> simp only [conditionedPairSubstitution]
  · exact le_rfl
  · split_ifs <;> norm_num

/-- INTERNAL: Fixing one selected label per assigned pair reduces the degree
of the selected-element polynomial by exactly the number of assigned pairs.
TEXLINE: main.tex:403-407 -/
theorem conditioned_pair_homogeneous {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) :
    (conditionedPairPolynomial M₁ M₂ q σ).IsHomogeneous
      (n - (assignedPairs σ).card) := by
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
  have hbase : ((MvPolynomial.pderiv none)^[n] T).IsHomogeneous n := by
    simpa only [show 2 * n - n = n by omega] using hiter n
  have hfold := derivative_fold_homogeneous (assignedPairs σ).toList
    (fun i => some (i, (σ i).getD false)) _ n hbase
  simpa [conditionedPairPolynomial, T] using
    (linear_substitution_homogeneous (conditionedPairSubstitution σ) _ _ hfold).C_mul
      (q ^ n / (n.factorial : ℚ))

/-- INTERNAL: Ordinary-pair extraction also consists only of the signature
input's allowed derivatives and nonnegative substitutions.
TEXLINE: main.tex:369-373,408-417 -/
theorem retained_descendant {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) (retained : Finset (Fin n)) :
    Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin n)
      (retainedPolynomial M₁ M₂ q σ retained) := by
  have hfold (l : List (Fin n)) (g : MvPolynomial (Fin n) ℚ)
      (hg : Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin n) g) :
      Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin n)
        (l.foldl (fun p i => extractOne i p) g) := by
    induction l generalizing g with
    | nil => exact hg
    | cons i l ih =>
      apply ih
      apply Descendant.substitute _ _ (Descendant.derivative i hg)
      intro s t
      split_ifs <;> norm_num
  exact hfold _ _ (conditioned_pair_descendant M₁ M₂ q hq σ)

/-- INTERNAL: After fixing assigned pairs and extracting every ordinary
unassigned pair, the degree is the number of retained unassigned pairs.
TEXLINE: main.tex:408-417 -/
theorem retained_homogeneous {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (retained : Finset (Fin n))
    (hretained : ∀ i ∈ retained, σ i = none) :
    (retainedPolynomial M₁ M₂ q σ retained).IsHomogeneous retained.card := by
  classical
  have hdisj : Disjoint (assignedPairs σ) retained := by
    rw [Finset.disjoint_left]
    intro i hi hr
    have hsome : σ i ≠ none := (Finset.mem_filter.mp hi).2
    exact hsome (hretained i hr)
  have hcount :
      (Finset.univ \ (assignedPairs σ ∪ retained)).card +
        (assignedPairs σ).card + retained.card = n := by
    have h := Finset.card_sdiff_add_card_eq_card
      (Finset.subset_univ (assignedPairs σ ∪ retained))
    rw [Finset.card_union_of_disjoint hdisj] at h
    simpa [Nat.add_assoc] using h
  have hfold (l : List (Fin n)) (g : MvPolynomial (Fin n) ℚ) (d : ℕ)
      (hg : g.IsHomogeneous d) :
      (l.foldl (fun p i => extractOne i p) g).IsHomogeneous (d - l.length) := by
    induction l generalizing g d with
    | nil => simpa using hg
    | cons i l ih =>
      have hi := linear_substitution_homogeneous
        (fun s t : Fin n => if s = i then 0 else if s = t then 1 else 0)
        _ _ (hg.pderiv (i := i))
      simpa [extractOne, Nat.sub_sub, Nat.add_comm] using ih _ (d - 1) hi
  have h := hfold (Finset.univ \ (assignedPairs σ ∪ retained)).toList _ _
    (conditioned_pair_homogeneous M₁ M₂ q σ)
  have hd : n - (assignedPairs σ).card -
      (Finset.univ \ (assignedPairs σ ∪ retained)).toList.length = retained.card := by
    rw [Finset.length_toList]
    omega
  simpa only [retainedPolynomial, hd] using h

/-- INTERNAL: Retain the two distinguished coordinates after conditioning.
TEXLINE: main.tex:408-412 -/
noncomputable def pairSubstitutionTwo {n : ℕ} (i j : Fin n) : Fin n → Fin 2 → ℚ :=
  fun s t => if s = i ∧ t = 0 then 1 else if s = j ∧ t = 1 then 1 else 0

/-- INTERNAL: The actual conditioned two-pair quadratic in the determinant
argument, rather than a matrix defined from the desired inequalities.
TEXLINE: main.tex:408-412 -/
noncomputable def conditionedPairQuadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (i j : Fin n) : MvPolynomial (Fin 2) ℚ :=
  linearSubstitution (pairSubstitutionTwo i j) (retainedPolynomial M₁ M₂ q σ {i, j})

/-- INTERNAL: The actual conditioned three-pair quadratic, including the
last derivative at k prescribed in the paper.
TEXLINE: main.tex:412-417 -/
noncomputable def conditionedTripleQuadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (i j k : Fin n) : MvPolynomial (Fin 3) ℚ :=
  linearSubstitution (tripleSubstitution i j k)
    (MvPolynomial.pderiv k (retainedPolynomial M₁ M₂ q σ {i, j, k}))

/-- INTERNAL: The two-pair polynomial is a homogeneous quadratic descendant
for every assignment leaving i and j unassigned.
TEXLINE: main.tex:403-412 -/
theorem conditioned_pair_quadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) (i j : Fin n)
    (hij : i ≠ j) (hi : σ i = none) (hj : σ j = none) :
    Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin 2)
      (conditionedPairQuadratic M₁ M₂ q σ i j) ∧
      (conditionedPairQuadratic M₁ M₂ q σ i j).IsHomogeneous 2 := by
  classical
  constructor
  · apply Descendant.substitute _ _ (retained_descendant M₁ M₂ q hq σ {i, j})
    intro s t
    unfold pairSubstitutionTwo
    split_ifs <;> norm_num
  · have hret := retained_homogeneous M₁ M₂ q σ {i, j} (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> assumption)
    have hc : ({i, j} : Finset (Fin n)).card = 2 := by simp [hij]
    rw [hc] at hret
    exact linear_substitution_homogeneous _ _ _ hret

/-- INTERNAL: The three-pair polynomial is a homogeneous quadratic descendant
for every assignment leaving i, j and k unassigned.
TEXLINE: main.tex:403-417 -/
theorem conditioned_triple_quadratic {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k)
    (hi : σ i = none) (hj : σ j = none) (hk : σ k = none) :
    Descendant (tuttePolynomial (pairedMatroid M₁ M₂) q) (Fin 3)
      (conditionedTripleQuadratic M₁ M₂ q σ i j k) ∧
      (conditionedTripleQuadratic M₁ M₂ q σ i j k).IsHomogeneous 2 := by
  classical
  constructor
  · apply Descendant.substitute _ _
      (Descendant.derivative k (retained_descendant M₁ M₂ q hq σ {i, j, k}))
    intro s t
    unfold tripleSubstitution
    split_ifs <;> norm_num
  · have hret := retained_homogeneous M₁ M₂ q σ {i, j, k} (by
      intro s hs
      simp only [Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl | rfl <;> assumption)
    have hc : ({i, j, k} : Finset (Fin n)).card = 3 := by simp [hij, hjk, hik]
    rw [hc] at hret
    exact linear_substitution_homogeneous _ _ _ (hret.pderiv (i := k))

end CountingMatroid.Analysis.ConditionalDefectQuadratics
