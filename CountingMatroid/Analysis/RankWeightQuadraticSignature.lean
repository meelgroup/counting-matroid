import CountingMatroid.Model.Prelude
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
The precise external signature input, separate from the operational rank
correspondence and coefficient extraction proved in the counting paper.
`Descendant` records only partial derivatives, nonnegative linear
substitutions, and nonnegative scalar multiplication. The signature uses
Mathlib's maximum dimension of a positive definite subspace over the reals.
The empty- and singleton-ground signature cases are proved, using the
homogeneous-degree invariant of every descendant. The signature case with
at most one output variable follows from the ambient dimension bound. The remaining
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
          have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos hnonpos
          have hnull := l.finrank_range_add_finrank_ker
          have hrange : Module.finrank ℝ (LinearMap.range l) ≤ 1 := by
            simpa using (LinearMap.range l).finrank_le
          change sigPos Q ≤ 1
          omega
        -- BLOCKER: the degree and nonnegative-coefficient invariants above
        -- do not prove nonpositivity on ker (Q.associated e). This is the
        -- missing Lorentzian invariant, including its preservation under
        -- nonnegative substitutions. Current searches by statement shape
        -- found no polynomial result in Mathlib's matroid API, no polynomial
        -- log-concavity/stability or Lorentzian API in Mathlib or Arlib, and
        -- no spectral bound that supplies this matroid-polynomial premise.
        -- The generic signature/dimension lemmas only finish the argument
        -- after hnonpos; they do not establish it. The outstanding branch
        -- has at least two ground elements and at least two output variables.
        -- PRIOR-PROPOSAL: this unchanged quadratic consequence is explicitly
        -- borrowed at main.tex:334-348 from BH2020, Theorems 4.10, 2.10,
        -- and Corollary 2.11, together with the defining quadratic signature.
        -- hQe is proved, so the kernel is the orthogonal complement of an
        -- actual positive vector; rank-nullity completes the signature
        -- bound once this remaining nonpositivity goal is established.
        sorry
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

* 2026-10-09 · partial · proved the at-most-one-output-variable branch using sigPos_le_finrank and Module.finrank_pi; preserved all earlier homogeneous-degree, coefficient-cone and small-ground proofs. Current statement-shape searches found no matroid-polynomial, Lorentzian closure or substitute spectral declaration supplying nonpositivity on the positive-vector orthogonal complement. The remaining cited Bränden–Huh input stays open in its original theorem, without new helpers or assumptions.
* 2026-10-09 · blocked · preserved the proved empty-ground branch; searched project, pinned Mathlib and Arlib for Lorentzian rank-weight base, closure and quadratic signature results without finding an applicable declaration. A stdin application of descendant_constant to the nonempty branch fails because its initial polynomial must be constant. Proposed the unchanged cited Bränden–Huh consequence as prior input; introduced no helper or assumption.
-/
