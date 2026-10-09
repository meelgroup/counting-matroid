import CountingMatroid.Model.Prelude
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Real.Basic
import CountingMatroid.Analysis.LinearPolynomialChainRule
import CountingMatroid.Analysis.LinearSubstitutionHessian
import CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
import CountingMatroid.Analysis.BinaryRankWeightSignature
import CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The two-element ground
case is proved by rank submodularity and a two-square calculation, with
the resulting hyperplane transported through every allowed substitution.
The signature case with at most one output variable follows from the ambient
dimension bound. The remaining
Bränden–Huh input is the unresolved borrowed mixed-derivative prerequisite
in `MixedDirectionalRankWeightSignature`. The exact normal
form of a descendant is proved: nonnegative directional derivatives in the
original variables, followed by one nonnegative linear substitution and a
nonnegative scalar. A nonzero quadratic uses exactly ground-set size minus
two derivatives. The unresolved signature bound is applied to this normal
form. A proved nonpositive-hyperplane invariant transports the Hessian
through the final substitution and scaling and recovers the exact orthogonal
kernel used by the signature bound. Only its establishment for the original
mixed directional derivative on ground sets of size at least three remains
open in that support module; no Lorentzian assumption has been introduced.
-/

namespace CountingMatroid.Analysis.RankWeightQuadraticSignature

open scoped BigOperators

/-- PAPER: main.tex:334-339
The homogenized rank-weight polynomial in the cited Bränden–Huh theorem.
The extra `none` variable is the paper's homogenizing variable z₀. -/
noncomputable def tuttePolynomial {α : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) : MvPolynomial (Option α) ℚ := by
  classical
  exact ∑ A : Finset α,
    MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
      MvPolynomial.X none ^ (Fintype.card α - A.card) *
        ∏ a ∈ A, MvPolynomial.X (some a)

/-- INTERNAL: Encode the paper's allowed nonnegative linear substitutions
as polynomial evaluation, including zero columns and identified variables.
TEXLINE: main.tex:326-343 -/
noncomputable def linearSubstitution {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) : MvPolynomial τ ℚ :=
  MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p

/-- INTERNAL: A finite derivation by exactly the operations used in the
paper's quadratic extraction; the variable type can change on substitution.
TEXLINE: main.tex:326-373 -/
inductive Descendant {σ : Type} (p : MvPolynomial σ ℚ) :
    (τ : Type) → MvPolynomial τ ℚ → Prop
  | initial : Descendant p σ p
  | derivative {τ : Type} {g : MvPolynomial τ ℚ} (t : τ) :
      Descendant p τ g → Descendant p τ (MvPolynomial.pderiv t g)
  | substitute {τ υ : Type} [Fintype υ] {g : MvPolynomial τ ℚ}
      (a : τ → υ → ℚ) (ha : ∀ s t, 0 ≤ a s t) :
      Descendant p τ g → Descendant p υ (linearSubstitution a g)
  | scale {τ : Type} {g : MvPolynomial τ ℚ} (c : ℚ) (hc : 0 ≤ c) :
      Descendant p τ g → Descendant p τ (MvPolynomial.C c * g)

/-- INTERNAL: Hessian of a quadratic polynomial, with rational entries
cast to the real field in which the signature theorem is stated.
TEXLINE: main.tex:326-343 -/
noncomputable def hessian {τ : Type} (g : MvPolynomial τ ℚ) : Matrix τ τ ℝ :=
  fun s t => (MvPolynomial.constantCoeff
    (MvPolynomial.pderiv s (MvPolynomial.pderiv t g)) : ℚ)

/-- INTERNAL: Compute a Hessian entry directly from a degree-two coefficient;
the repeated-variable coefficient has multiplicity two.
TEXLINE: main.tex:408-417 -/
theorem hessian_coefficient {τ : Type} [DecidableEq τ]
    (g : MvPolynomial τ ℚ) (s t : τ) :
    hessian g s t =
      ((g.coeff (Finsupp.single s 1 + Finsupp.single t 1) *
        (if s = t then 2 else 1) : ℚ) : ℝ) := by
  classical
  unfold hessian
  rw [MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
    MvPolynomial.coeff_pderiv]
  by_cases h : s = t
  · subst t
    norm_num
  · simp [h, Finsupp.single_apply, Ne.symm h]

/-- INTERNAL: Differentiation and nonnegative linear substitutions cannot
turn a constant into a polynomial of positive degree. -/
theorem descendant_constant {σ τ : Type} (c : ℚ) (g : MvPolynomial τ ℚ)
    (hg : Descendant (MvPolynomial.C c : MvPolynomial σ ℚ) τ g) :
    ∃ d : ℚ, g = MvPolynomial.C d := by
  induction hg with
  | initial => exact ⟨c, rfl⟩
  | derivative t _ ih =>
    obtain ⟨d, rfl⟩ := ih
    exact ⟨0, by simp⟩
  | substitute a ha _ ih =>
    obtain ⟨d, rfl⟩ := ih
    exact ⟨d, by simp [linearSubstitution]⟩
  | scale k hk _ ih =>
    obtain ⟨d, rfl⟩ := ih
    exact ⟨k * d, by simp⟩

/-- PAPER: main.tex:334-339
Every term of the homogenized rank-weight polynomial has ground-set degree. -/
theorem tuttePolynomial_isHomogeneous {α : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) :
    (tuttePolynomial N q).IsHomogeneous (Fintype.card α) := by
  classical
  unfold tuttePolynomial
  apply MvPolynomial.IsHomogeneous.sum
  intro A _
  have hprod : (∏ a ∈ A, MvPolynomial.X (some a) :
      MvPolynomial (Option α) ℚ).IsHomogeneous A.card := by
    simpa using MvPolynomial.IsHomogeneous.prod A
      (fun a => (MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ))
      (fun _ => 1) (fun a _ => MvPolynomial.isHomogeneous_X ℚ (some a))
  have hterm := ((MvPolynomial.isHomogeneous_X_pow
    (R := ℚ) (none : Option α) (Fintype.card α - A.card)).C_mul
      ((q ^ (N.eRk (A : Set α)).toNat)⁻¹)).mul hprod
  simpa only [Nat.sub_add_cancel A.card_le_univ] using hterm

/-- INTERNAL: Linear substitution preserves homogeneous degree, including
zero columns and identification of variables.
TEXLINE: main.tex:326-343 -/
theorem linearSubstitution_isHomogeneous {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (d : ℕ)
    (hp : p.IsHomogeneous d) : (linearSubstitution a p).IsHomogeneous d := by
  unfold linearSubstitution
  simpa only [one_mul] using hp.aeval
    (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t)
    (fun s => MvPolynomial.IsHomogeneous.sum Finset.univ _ 1
      (fun t _ => MvPolynomial.isHomogeneous_C_mul_X (a s t) t))

/-- INTERNAL: The homogeneous-degree invariant of a descendant derivation:
derivatives decrease degree, and the remaining operations preserve it.
TEXLINE: main.tex:334-348 -/
theorem descendant_homogeneous_degree_le {σ τ : Type}
    (p : MvPolynomial σ ℚ) (g : MvPolynomial τ ℚ) (d : ℕ)
    (hp : p.IsHomogeneous d) (hg : Descendant p τ g) :
    ∃ k ≤ d, g.IsHomogeneous k := by
  induction hg with
  | initial => exact ⟨d, le_rfl, hp⟩
  | derivative t _ ih =>
    obtain ⟨k, hk, hhom⟩ := ih
    exact ⟨k - 1, (Nat.sub_le _ _).trans hk, hhom.pderiv⟩
  | substitute a ha _ ih =>
    obtain ⟨k, hk, hhom⟩ := ih
    exact ⟨k, hk, linearSubstitution_isHomogeneous a _ k hhom⟩
  | scale c hc _ ih =>
    obtain ⟨k, hk, hhom⟩ := ih
    exact ⟨k, hk, hhom.C_mul c⟩

/-- INTERNAL: The coefficient cone is an invariant of the entire descendant
derivation, including substitutions that introduce or merge variables.
TEXLINE: main.tex:334-348 -/
theorem tutte_descendant_coeff_nonneg {α τ : Type} [Fintype α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (g : MvPolynomial τ ℚ)
    (hg : Descendant (tuttePolynomial N q) τ g) :
    ∀ d, 0 ≤ g.coeff d := by
  classical
  have hmul {υ : Type} (p₁ p₂ : MvPolynomial υ ℚ)
      (h₁ : ∀ d, 0 ≤ p₁.coeff d) (h₂ : ∀ d, 0 ≤ p₂.coeff d) :
      ∀ d, 0 ≤ (p₁ * p₂).coeff d := by
    intro d
    rw [MvPolynomial.coeff_mul]
    exact Finset.sum_nonneg (fun m _ => mul_nonneg (h₁ m.1) (h₂ m.2))
  have hpow {υ : Type} (p : MvPolynomial υ ℚ)
      (hp : ∀ d, 0 ≤ p.coeff d) (k : ℕ) :
      ∀ d, 0 ≤ (p ^ k).coeff d := by
    induction k with
    | zero => intro d; simp only [pow_zero, MvPolynomial.coeff_one]; split_ifs <;> norm_num
    | succ k ih => rw [pow_succ]; exact hmul _ _ ih hp
  have hprod {ι υ : Type} (S : Finset ι) (p : ι → MvPolynomial υ ℚ)
      (hp : ∀ i ∈ S, ∀ d, 0 ≤ (p i).coeff d) :
      ∀ d, 0 ≤ (∏ i ∈ S, p i).coeff d := by
    induction S using Finset.induction_on with
    | empty => intro d; simp only [Finset.prod_empty, MvPolynomial.coeff_one]; split_ifs <;> norm_num
    | @insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact hmul _ _ (hp i (by simp)) (ih (fun j hj => hp j (by simp [hj])))
  have hbase : ∀ d, 0 ≤ (tuttePolynomial N q).coeff d := by
    intro d
    unfold tuttePolynomial
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro A _
    rw [mul_assoc, MvPolynomial.coeff_C_mul]
    apply mul_nonneg (inv_nonneg.mpr (pow_pos hq _).le)
    apply hmul
    · intro m; rw [MvPolynomial.coeff_X_pow]; split_ifs <;> norm_num
    · exact hprod A (fun a => MvPolynomial.X (some a))
        (fun a _ m => by rw [MvPolynomial.coeff_X]; split_ifs <;> norm_num)
  induction hg with
  | initial => exact hbase
  | derivative t _ ih =>
    intro d
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (ih _) (by positivity)
  | @substitute τ υ _ p a ha hp ih =>
    let L := fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t
    have hL : ∀ s d, 0 ≤ (L s).coeff d := by
      intro s d
      dsimp only [L]
      rw [MvPolynomial.coeff_sum]
      apply Finset.sum_nonneg
      intro t _
      rw [MvPolynomial.coeff_C_mul]
      exact mul_nonneg (ha s t) (by rw [MvPolynomial.coeff_X]; split_ifs <;> norm_num)
    intro d
    unfold linearSubstitution
    rw [p.as_sum, map_sum, MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro m _
    rw [MvPolynomial.aeval_monomial]
    change 0 ≤ (MvPolynomial.C (p.coeff m) *
      m.prod (fun s k => L s ^ k)).coeff d
    rw [MvPolynomial.coeff_C_mul]
    apply mul_nonneg (ih m)
    exact hprod m.support _ (fun s _ => hpow (L s) (hL s) (m s)) d
  | scale c hc _ ih =>
    intro d
    rw [MvPolynomial.coeff_C_mul]
    exact mul_nonneg hc (ih d)

/-- INTERNAL: Every intermediate variable type in a descendant of a finite
variable polynomial is finite, even though the constructors do not carry
this instance explicitly.
TEXLINE: main.tex:326-348 -/
theorem descendant_finite_variables {σ τ : Type} [Finite σ]
    (p : MvPolynomial σ ℚ) (g : MvPolynomial τ ℚ) (hg : Descendant p τ g) :
    Finite τ := by
  induction hg with
  | initial => infer_instance
  | derivative _ _ ih => exact ih
  | substitute _ _ _ _ => infer_instance
  | scale _ _ _ ih => exact ih

/-- INTERNAL: Iterated directional differentiation in the original variable
space. The list head is the last derivative applied.
TEXLINE: main.tex:326-348 -/
noncomputable def iteratedDirectionalDerivative {σ : Type} [Fintype σ]
    (ds : List (σ → ℚ)) (p : MvPolynomial σ ℚ) : MvPolynomial σ ℚ :=
  match ds with
  | [] => p
  | d :: ds => ∑ s, MvPolynomial.C (d s) *
      MvPolynomial.pderiv s (iteratedDirectionalDerivative ds p)

/-- INTERNAL: Normalize the whole descendant derivation into nonnegative
directional derivatives in the original variable space followed by one
nonnegative linear substitution and one nonnegative scalar. This is an exact
polynomial identity, not an assumed Lorentzian closure property.
TEXLINE: main.tex:326-348 -/
theorem descendant_directional_normal_form {σ τ : Type} [instσ : Fintype σ]
    (p : MvPolynomial σ ℚ) (g : MvPolynomial τ ℚ) (hg : Descendant p τ g) :
    ∀ [Fintype τ], ∃ (c : ℚ) (a : σ → τ → ℚ) (ds : List (σ → ℚ)),
      0 ≤ c ∧ (∀ s t, 0 ≤ a s t) ∧ (∀ d ∈ ds, ∀ s, 0 ≤ d s) ∧
      g = MvPolynomial.C c * linearSubstitution a (iteratedDirectionalDerivative ds p) := by
  classical
  induction hg with
  | initial =>
    intro instσ'
    cases Subsingleton.elim instσ' instσ
    refine ⟨1, (fun s t => if s = t then 1 else 0), [], by norm_num,
      (by intro s t; dsimp; split_ifs <;> norm_num), (by simp), ?_⟩
    simpa [iteratedDirectionalDerivative, linearSubstitution] using
      (MvPolynomial.aeval_X_left_apply p).symm
  | @derivative τ g t hg ih =>
    intro _
    obtain ⟨c, a, ds, hc, ha, hds, hrepr⟩ := ih
    refine ⟨c, a, (fun s => a s t) :: ds, hc, ha, ?_, ?_⟩
    · intro d hd s
      rcases List.mem_cons.mp hd with rfl | hd
      · exact ha s t
      · exact hds d hd s
    · rw [hrepr, MvPolynomial.pderiv_C_mul]
      congr 1
      exact LinearPolynomialChainRule.linear_aeval_pderiv a _ t
  | @substitute τ υ instυ g b hb hg ih =>
    intro instυ'
    cases Subsingleton.elim instυ' instυ
    haveI : Finite τ := descendant_finite_variables p g hg
    letI : Fintype τ := Fintype.ofFinite τ
    obtain ⟨c, a, ds, hc, ha, hds, hrepr⟩ := ih
    refine ⟨c, (fun s u => ∑ t, a s t * b t u), ds, hc, ?_, hds, ?_⟩
    · intro s u
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (ha s t) (hb t u))
    · rw [hrepr]
      unfold linearSubstitution
      rw [map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
        LinearPolynomialChainRule.linear_aeval_comp]
  | scale k hk hg ih =>
    intro _
    obtain ⟨c, a, ds, hc, ha, hds, hrepr⟩ := ih
    refine ⟨k * c, a, ds, mul_nonneg hk hc, ha, hds, ?_⟩
    rw [hrepr, ← mul_assoc, ← MvPolynomial.C.map_mul]

/-- INTERNAL: The degree of an iterated directional derivative decreases
by the number of directions, with truncated subtraction covering zero.
TEXLINE: main.tex:334-348 -/
theorem iteratedDirectionalDerivative_isHomogeneous {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (d : ℕ) (hp : p.IsHomogeneous d)
    (ds : List (σ → ℚ)) :
    (iteratedDirectionalDerivative ds p).IsHomogeneous (d - ds.length) := by
  induction ds with
  | nil => simpa [iteratedDirectionalDerivative] using hp
  | cons a ds ih =>
    have h := MvPolynomial.IsHomogeneous.sum Finset.univ
      (fun s => MvPolynomial.C (a s) *
        MvPolynomial.pderiv s (iteratedDirectionalDerivative ds p))
      (d - ds.length - 1) (fun s _ => ih.pderiv.C_mul (a s))
    simpa [iteratedDirectionalDerivative, Nat.sub_sub] using h

/-- INTERNAL: Identify the parent's directional-derivative recursion with
the library-list fold used by the independent mixed-derivative prerequisite.
TEXLINE: main.tex:334-348 -/
theorem iteratedDirectionalDerivative_eq_foldr {σ : Type} [Fintype σ]
    (ds : List (σ → ℚ)) (p : MvPolynomial σ ℚ) :
    iteratedDirectionalDerivative ds p =
      ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp only [iteratedDirectionalDerivative, List.foldr_cons, ih]

/-- INTERNAL: Scalar multiplication of a rational polynomial scales its
real Hessian quadratic form by the same scalar.
TEXLINE: main.tex:326-348 -/
theorem hessian_C_mul {τ : Type} [Fintype τ] [DecidableEq τ]
    (c : ℚ) (p : MvPolynomial τ ℚ) :
    (hessian (MvPolynomial.C c * p)).toQuadraticForm' =
      (c : ℝ) • (hessian p).toQuadraticForm' := by
  have hmat : hessian (MvPolynomial.C c * p) = (c : ℝ) • hessian p := by
    ext i j
    simp [hessian]
  rw [hmat]
  unfold Matrix.toQuadraticForm'
  rw [map_smul, LinearMap.BilinMap.toQuadraticMap_smul]

/-- INTERNAL: Linear substitution of a rational polynomial pulls back its
real Hessian quadratic form, including singular substitutions.
TEXLINE: main.tex:326-348 -/
theorem hessian_linearSubstitution {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    (hessian (linearSubstitution a p)).toQuadraticForm' =
      (hessian p).toQuadraticForm'.comp (Matrix.toLin' (fun s t => (a s t : ℝ))) := by
  exact LinearSubstitutionHessian.linear_aeval_hessian_quadraticForm a p

/-- PAPER: main.tex:334-348
BORROWED: Bränden–Huh, Lorentzian polynomials (2020), Theorems 4.10,
2.10 and Corollary 2.11, together with the defining quadratic signature.
Only their quadratic consequence is required, after a finite sequence of
the cited closure operations. This does not assert any operational rank
identity or identify any partition coefficient. -/
theorem branden_huh_quadratic_signature {α τ : Type} [Fintype α] [Fintype τ]
    [DecidableEq τ] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) (g : MvPolynomial τ ℚ)
    (hg : Descendant (tuttePolynomial N q) τ g)
    (hdegree : g.IsHomogeneous 2) :
    sigPos (hessian g).toQuadraticForm' ≤ 1 := by
  classical
  by_cases hτsmall : Fintype.card τ ≤ 1
  · have hd := sigPos_le_finrank (hessian g).toQuadraticForm'
    rw [Module.finrank_pi] at hd
    exact hd.trans hτsmall
  by_cases hempty : Fintype.card α = 0
  · haveI : IsEmpty α := Fintype.card_eq_zero_iff.mp hempty
    have hU : (Finset.univ : Finset (Finset α)) = {∅} := by
      ext A
      simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
      exact Subsingleton.elim A ∅
    have hT : tuttePolynomial N q = MvPolynomial.C 1 := by
      unfold tuttePolynomial
      rw [hU, Finset.sum_singleton]
      simp only [Finset.coe_empty, Matroid.eRk_empty, ENat.toNat_zero,
        pow_zero, inv_one, Finset.card_empty, Nat.sub_zero, hempty,
        Finset.prod_empty, mul_one]
    rw [hT] at hg
    obtain ⟨c, rfl⟩ := descendant_constant 1 g hg
    have hz : hessian (MvPolynomial.C c : MvPolynomial τ ℚ) = 0 := by
      ext s t
      simp [hessian]
    rw [hz]
    have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
      (Q := (0 : Matrix τ τ ℝ).toQuadraticForm') (V := ⊤)
      (by intro v hv; simp [Matrix.toQuadraticForm'])
    have htop : Module.finrank ℝ (⊤ : Submodule ℝ (τ → ℝ)) =
        Module.finrank ℝ (τ → ℝ) := by simp
    rw [htop] at hdim
    omega
  ·
    obtain ⟨k, hk, hhom⟩ := descendant_homogeneous_degree_le
      (tuttePolynomial N q) g (Fintype.card α)
      (tuttePolynomial_isHomogeneous N q) hg
    by_cases hsmall : Fintype.card α < 2
    · have hgzero : g = 0 := by
        by_contra hne
        have heq := hhom.inj_right hdegree hne
        omega
      rw [hgzero]
      have hz : hessian (0 : MvPolynomial τ ℚ) = 0 := by
        ext s t
        simp [hessian]
      rw [hz]
      have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
        (Q := (0 : Matrix τ τ ℝ).toQuadraticForm') (V := ⊤)
        (by intro v hv; simp [Matrix.toQuadraticForm'])
      have htop : Module.finrank ℝ (⊤ : Submodule ℝ (τ → ℝ)) =
          Module.finrank ℝ (τ → ℝ) := by simp
      rw [htop] at hdim
      omega
    · have hcoeff := tutte_descendant_coeff_nonneg N q hq g hg
      have hentry (s t : τ) : 0 ≤ hessian g s t := by
        rw [hessian_coefficient]
        exact_mod_cast mul_nonneg (hcoeff _)
          (show (0 : ℚ) ≤ if s = t then 2 else 1 by split_ifs <;> norm_num)
      by_cases hpositive : ∃ s t, 0 < hessian g s t
      · let Q := (hessian g).toQuadraticForm'
        let e : τ → ℝ := fun _ => 1
        have hQe : 0 < Q e := by
          obtain ⟨s, t, hst⟩ := hpositive
          have hrow : 0 < ∑ t, hessian g s t :=
            Finset.sum_pos' (fun t _ => hentry s t)
              ⟨t, Finset.mem_univ t, hst⟩
          have hsum : 0 < ∑ s, ∑ t, hessian g s t :=
            Finset.sum_pos' (fun s _ => Finset.sum_nonneg (fun t _ => hentry s t))
              ⟨s, Finset.mem_univ s, hrow⟩
          simpa [Q, e, Matrix.toQuadraticForm', Matrix.toLinearMap₂'_apply] using hsum
        letI : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
        let l : (τ → ℝ) →ₗ[ℝ] ℝ := Q.associated e
        suffices hnonpos : ∀ v ∈ LinearMap.ker l, Q v ≤ 0 by
          exact QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.sigPos_le_one
            ⟨l, fun v hv => hnonpos v (LinearMap.mem_ker.mpr hv)⟩
        have hgne : g ≠ 0 := by
          intro hgzero
          have hz : hessian g = 0 := by
            rw [hgzero]
            ext s t
            simp [hessian]
          have hzero : Q e = 0 := by
            simp [Q, hz, Matrix.toQuadraticForm']
          linarith
        obtain ⟨c, a, ds, hc, ha, hds, hrepr⟩ :=
          descendant_directional_normal_form (tuttePolynomial N q) g hg
        have hnormaldegree : g.IsHomogeneous (Fintype.card α - ds.length) := by
          rw [hrepr]
          exact (linearSubstitution_isHomogeneous a _ _
            (iteratedDirectionalDerivative_isHomogeneous _ _
              (tuttePolynomial_isHomogeneous N q) ds)).C_mul c
        have hlength : ds.length + 2 = Fintype.card α := by
          have heq := hnormaldegree.inj_right hdegree hgne
          omega
        have hcpos : 0 < c := by
          have hcne : c ≠ 0 := by
            intro hc0
            apply hgne
            simp [hrepr, hc0]
          exact lt_of_le_of_ne hc hcne.symm
        have hsource : QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane
            (hessian (iteratedDirectionalDerivative ds (tuttePolynomial N q))).toQuadraticForm' := by
          by_cases htwo : Fintype.card α = 2
          · have hdszero : ds = [] := List.length_eq_zero_iff.mp (by omega)
            rw [hdszero]
            dsimp only [iteratedDirectionalDerivative]
            exact BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
              N q hq hqone htwo
          · rw [iteratedDirectionalDerivative_eq_foldr]
            exact MixedDirectionalRankWeightSignature.mixed_directional_rank_weight_nonpositive_hyperplane
              N hfull q hq hqone ds hds hlength
        have htransform : Q = (c : ℝ) •
            (hessian (iteratedDirectionalDerivative ds (tuttePolynomial N q))).toQuadraticForm'.comp
              (Matrix.toLin' (fun s t => (a s t : ℝ))) := by
          dsimp only [Q]
          rw [hrepr, hessian_C_mul, hessian_linearSubstitution]
        have hwhole : QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane Q := by
          rw [htransform]
          exact (hsource.comp _).smul c (by exact_mod_cast hc)
        intro v hv
        exact hwhole.nonpos_of_associated_eq_zero e v hQe (LinearMap.mem_ker.mp hv)

      · have hz : hessian g = 0 := by
          ext s t
          have hnot : ¬ 0 < hessian g s t := fun hst => hpositive ⟨s, t, hst⟩
          exact le_antisymm (le_of_not_gt hnot) (hentry s t)
        rw [hz]
        have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
          (Q := (0 : Matrix τ τ ℝ).toQuadraticForm') (V := ⊤)
          (by intro v hv; simp [Matrix.toQuadraticForm'])
        have htop : Module.finrank ℝ (⊤ : Submodule ℝ (τ → ℝ)) =
            Module.finrank ℝ (τ → ℝ) := by simp
        rw [htop] at hdim
        omega

end CountingMatroid.Analysis.RankWeightQuadraticSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · handoff-ready · after the live scheduler opened capacity, isolated the sole remaining original-variable invariant in MixedDirectionalRankWeightSignature and proved the fold identity connecting it to the parent. All other children are proved; the parent uses the independent prerequisite and contains no remaining proof hole of its own. The prerequisite still has the mixed-directional compatibility gap, so this is a proof boundary, not a completed Bränden–Huh proof.
* 2026-10-09 · partial · proved Hessian congruence under linear substitution and scalar scaling, and the nonpositive-hyperplane invariant with its pullback, scaling, signature and positive-vector orthogonal-kernel consequences. Proved the two-element Tutte quadratic by the exact rank-weight pair bound and a two-square identity, so the parent closes every descendant on ground sets of size at most two. Its single remaining gap is establishment of the invariant for |α|≥3 after exactly |α|-2 nonnegative directional derivatives; all subsequent transport is proved. No new assumption or open child was introduced.
* 2026-10-09 · partial · proved the linear polynomial chain rule and substitution composition in LinearPolynomialChainRule, then proved finite intermediate variables, the exact directional normal form, and its homogeneous degree. The parent uses this representation and proves that its direction list has length |α|-2 and its scalar is positive. The original nonpositive-kernel gap now concerns this normalized expression. A stdin application of eRk_submod failed by statement shape; separate checked stdin examples show that adding two signature-one forms can produce signature two. The unresolved cited input is compatibility of mixed nonnegative directional derivatives of the common matroid polynomial, not the algebraic normalization. No assumption or new open helper was introduced.
* 2026-10-09 · partial · proved the at-most-one-output-variable branch using sigPos_le_finrank and Module.finrank_pi; preserved all earlier homogeneous-degree, coefficient-cone and small-ground proofs. Current statement-shape searches found no matroid-polynomial, Lorentzian closure or substitute spectral declaration supplying nonpositivity on the positive-vector orthogonal complement. The remaining cited Bränden–Huh input stays open in its original theorem, without new helpers or assumptions.
* 2026-10-09 · blocked · preserved the proved empty-ground branch; searched project, pinned Mathlib and Arlib for Lorentzian rank-weight base, closure and quadratic signature results without finding an applicable declaration. A stdin application of descendant_constant to the nonempty branch fails because its initial polynomial must be constant. Proposed the unchanged cited Bränden–Huh consequence as prior input; introduced no helper or assumption.
-/
