import CountingMatroid.Analysis.RankWeightQuadraticSignature

set_option autoImplicit false

/-! Squarefree label variables in the Tutte polynomial imply that three
derivatives in the sum of two label directions vanish. This uses no
operational rank or partition identification. -/

namespace CountingMatroid.Analysis.TwoLabelDerivativeNilpotence

open CountingMatroid.Analysis.RankWeightQuadraticSignature
open scoped BigOperators

/-- INTERNAL: Partial derivatives commute, including repeated variables.
TEXLINE: main.tex:354-373 -/
theorem derivative_commute {α : Type} (x y : α) (p : MvPolynomial α ℚ) :
    MvPolynomial.pderiv x (MvPolynomial.pderiv y p) =
      MvPolynomial.pderiv y (MvPolynomial.pderiv x p) := by
  classical
  ext d
  simp only [MvPolynomial.coeff_pderiv, Finsupp.add_apply, Finsupp.single_apply]
  by_cases h : x = y
  · subst y; rfl
  · simp [h, Ne.symm h, add_comm, add_left_comm]
    ring

/-- INTERNAL: Every selected label occurs at most once in a Tutte monomial.
TEXLINE: main.tex:334-339 -/
theorem tutte_label_squarefree {α : Type} [Fintype α] (N : Matroid α)
    (q : ℚ) (x : α) : (tuttePolynomial N q).degreeOf (some x) ≤ 1 := by
  classical
  unfold tuttePolynomial
  apply (MvPolynomial.degreeOf_sum_le _ _ _).trans
  apply Finset.sup_le
  intro A _
  apply (MvPolynomial.degreeOf_mul_le _ _ _).trans
  have hz : (MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
      MvPolynomial.X none ^ (Fintype.card α - A.card) :
        MvPolynomial (Option α) ℚ).degreeOf (some x) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply (MvPolynomial.degreeOf_C_mul_le _ _ _).trans
    exact le_of_eq (MvPolynomial.degreeOf_X_pow_of_ne _ (by simp))
  rw [hz, zero_add]
  apply (MvPolynomial.degreeOf_prod_le _ _ _).trans
  simp only [MvPolynomial.degreeOf_X, Option.some.injEq]
  simp
  split_ifs <;> omega

/-- INTERNAL: Differentiation cannot increase any individual variable degree.
TEXLINE: main.tex:369-373 -/
theorem derivative_degree_le {α : Type} (j x : α) (p : MvPolynomial α ℚ) :
    (MvPolynomial.pderiv j p).degreeOf x ≤ p.degreeOf x := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [MvPolynomial.coeff_pderiv] at hne
  have hm : d + Finsupp.single j 1 ∈ p.support :=
    MvPolynomial.mem_support_iff.mpr (by intro h; simp [h] at hne)
  have hle := MvPolynomial.le_degreeOf_of_mem_support x hm
  have hadd : d x ≤ (d + Finsupp.single j 1 : α →₀ ℕ) x := by
    simp only [Finsupp.add_apply]
    omega
  exact hadd.trans hle

/-- INTERNAL: A variable of degree at most one has vanishing second derivative.
TEXLINE: main.tex:334-339 -/
theorem squarefree_second_derivative {α : Type} (x : α) (p : MvPolynomial α ℚ)
    (hx : p.degreeOf x ≤ 1) :
    MvPolynomial.pderiv x (MvPolynomial.pderiv x p) = 0 := by
  classical
  ext d
  rw [MvPolynomial.coeff_pderiv, MvPolynomial.coeff_pderiv]
  have hzero : p.coeff (d + Finsupp.single x 1 + Finsupp.single x 1) = 0 := by
    apply MvPolynomial.notMem_support_iff.mp
    apply MvPolynomial.notMem_support_of_degreeOf_lt x
    simp only [Finsupp.add_apply, Finsupp.single_eq_same]
    omega
  simp [hzero]

/-- INTERNAL: The third derivative in the sum of two squarefree label
directions vanishes by the pigeonhole principle.
TEXLINE: main.tex:412-417 -/
theorem two_label_derivative_cube {α : Type} (x y : α) (p : MvPolynomial α ℚ)
    (hx : p.degreeOf x ≤ 1) (hy : p.degreeOf y ≤ 1) :
    let D := fun g : MvPolynomial α ℚ => MvPolynomial.pderiv x g + MvPolynomial.pderiv y g
    D (D (D p)) = 0 := by
  dsimp only
  have hxx := squarefree_second_derivative x p hx
  have hyy := squarefree_second_derivative y p hy
  have hxyx : MvPolynomial.pderiv x (MvPolynomial.pderiv y (MvPolynomial.pderiv x p)) = 0 := by
    rw [derivative_commute x y, hxx, map_zero]
  have hxxy : MvPolynomial.pderiv x (MvPolynomial.pderiv x (MvPolynomial.pderiv y p)) = 0 := by
    rw [derivative_commute x y p, hxyx]
  have hyxy : MvPolynomial.pderiv y (MvPolynomial.pderiv x (MvPolynomial.pderiv y p)) = 0 := by
    rw [derivative_commute y x, hyy, map_zero]
  have hyyx : MvPolynomial.pderiv y (MvPolynomial.pderiv y (MvPolynomial.pderiv x p)) = 0 := by
    rw [derivative_commute y x p, hyxy]
  simp only [map_add, hxx, hyy, hxyx, hxxy, hyxy, hyyx, add_zero, zero_add]

/-- INTERNAL: Homogenizing derivatives preserve the two-label cubic
nilpotence of the Tutte polynomial.
TEXLINE: main.tex:354-373,412-417 -/
theorem tutte_two_label_derivative_cube {α : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) (x y : α) (m : ℕ) :
    let p := (MvPolynomial.pderiv none)^[m] (tuttePolynomial N q)
    let D := fun g : MvPolynomial (Option α) ℚ =>
      MvPolynomial.pderiv (some x) g + MvPolynomial.pderiv (some y) g
    D (D (D p)) = 0 := by
  have hdegree (z : α) (l : ℕ) :
      ((MvPolynomial.pderiv none)^[l] (tuttePolynomial N q)).degreeOf (some z) ≤ 1 := by
    induction l with
    | zero => exact tutte_label_squarefree N q z
    | succ l ih =>
      rw [Function.iterate_succ_apply']
      exact (derivative_degree_le none (some z) _).trans ih
  exact two_label_derivative_cube (some x) (some y) _ (hdegree x m) (hdegree y m)

/-- INTERNAL: A substitution column supported at one source variable
transports its partial derivative exactly.
TEXLINE: main.tex:369-373,412-417 -/
theorem linear_substitution_derivative_single {α β : Type} [Fintype α] [Fintype β] [DecidableEq α]
    (a : α → β → ℚ) (s : α) (t : β)
    (hcolumn : ∀ u, a u t = if u = s then 1 else 0) (p : MvPolynomial α ℚ) :
    MvPolynomial.pderiv t (linearSubstitution a p) =
      linearSubstitution a (MvPolynomial.pderiv s p) := by
  classical
  unfold linearSubstitution
  rw [CountingMatroid.Analysis.LinearPolynomialChainRule.linear_aeval_pderiv]
  simp_rw [hcolumn]
  simp

end CountingMatroid.Analysis.TwoLabelDerivativeNilpotence
