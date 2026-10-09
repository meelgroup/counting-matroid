import CountingMatroid.Model.Prelude
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty-ground signature case is proved. The nonempty-ground
Bränden–Huh input below is an unresolved borrowed result: the pinned
Mathlib and Arlib sources supply no Lorentzian rank-weight polynomial
theorem or its closure properties.
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
    -- BLOCKER: unavailable library declaration. Searches of the project,
    -- pinned Mathlib and Arlib found no matroid rank-weight Lorentzian
    -- base theorem, derivative/substitution closure, or equivalent
    -- quadratic Hessian bound (BH2020, Theorems 4.10, 2.10, Corollary 2.11;
    -- main.tex:334-348). Mathlib's generic signature lemmas do not supply
    -- the required matroid-polynomial premise.
    -- The direct `descendant_constant 1 g hg` route was checked on stdin:
    -- Lean expects Descendant (MvPolynomial.C 1) τ g, whereas hg starts
    -- from tuttePolynomial N q. This helper handles the empty-ground
    -- branch only; it does not establish Lorentzianity or a signature
    -- invariant for a nonconstant initial polynomial.
    -- PRIOR-PROPOSAL: carry this declaration's unchanged quadratic
    -- consequence of the explicitly cited Bränden–Huh results.
    sorry

end CountingMatroid.Analysis.RankWeightQuadraticSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · blocked · preserved the proved empty-ground branch; searched project, pinned Mathlib and Arlib for Lorentzian rank-weight base, closure and quadratic signature results without finding an applicable declaration. A stdin application of descendant_constant to the nonempty branch fails because its initial polynomial must be constant. Proposed the unchanged cited Bränden–Huh consequence as prior input; introduced no helper or assumption.
-/
