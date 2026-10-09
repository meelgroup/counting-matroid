import CountingMatroid.Analysis.LorentzianDirectionalSignature
import CountingMatroid.Analysis.BinaryRankWeightSignature
import CountingMatroid.Analysis.RankWeightSupportExchange
import CountingMatroid.Analysis.RankWeightCoordinateSignature

set_option autoImplicit false

/-!
The matroid-specific coordinate certificate needed by the general Lorentzian
directional-closure theorem. Homogeneity and coefficient nonnegativity are
proved directly. Support exchange is proved in RankWeightSupportExchange
using the exact subset description of the support. The remaining coordinate
quadratic signatures are isolated in RankWeightCoordinateSignature, with the
cases of ground size at most two and two repeated leading label derivatives
verified. The parent uses both children.
The general coordinate signature remains open pending the cited Brändén–Huh
result or an independent proof; no directional conclusion is assumed here.
-/

namespace CountingMatroid.Analysis.RankWeightCoordinateLorentzian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: The directly verified degree and coefficient-cone components
of the matroid coordinate certificate. They do not assert a signature bound.
TEXLINE: main.tex:332-339 -/
theorem rank_weight_basic_invariants {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    p.IsHomogeneous (Fintype.card α) ∧ ∀ m, 0 ≤ p.coeff m := by
  classical
  dsimp only
  constructor
  · apply MvPolynomial.IsHomogeneous.sum
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
  · have hmul (f g : MvPolynomial (Option α) ℚ)
        (hf : ∀ m, 0 ≤ f.coeff m) (hg : ∀ m, 0 ≤ g.coeff m) :
        ∀ m, 0 ≤ (f * g).coeff m := by
      intro m
      rw [MvPolynomial.coeff_mul]
      exact Finset.sum_nonneg (fun t _ => mul_nonneg (hf t.1) (hg t.2))
    have hprod (A : Finset α) :
        ∀ m, 0 ≤ (∏ a ∈ A, MvPolynomial.X (some a) :
          MvPolynomial (Option α) ℚ).coeff m := by
      induction A using Finset.induction_on with
      | empty =>
        intro m
        simp only [Finset.prod_empty, MvPolynomial.coeff_one]
        split_ifs <;> norm_num
      | @insert a A ha ih =>
        rw [Finset.prod_insert ha]
        exact hmul _ _ (fun m => by
          rw [MvPolynomial.coeff_X]
          split_ifs <;> norm_num) ih
    intro m
    rw [MvPolynomial.coeff_sum]
    apply Finset.sum_nonneg
    intro A _
    rw [mul_assoc, MvPolynomial.coeff_C_mul]
    apply mul_nonneg (inv_nonneg.mpr (pow_pos hq _).le)
    exact hmul _ _ (fun m => by
      rw [MvPolynomial.coeff_X_pow]
      split_ifs <;> norm_num) (hprod A) m

/-- PAPER: main.tex:334-348
The coordinate certificate for the homogenized matroid rank-weight polynomial.
This is the matroid-specific input, separated from the general theorem about
nonnegative directional derivatives.
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Theorem 4.10
supplies Lorentzianity, hence its coordinate quadratic signatures. The support
exchange component is verified directly from the subset exponents. -/
theorem rank_weight_coordinate_lorentzian {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) :
    CoordinateLorentzian
      (∑ A : Finset α,
        MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ a ∈ A, MvPolynomial.X (some a))
      (Fintype.card α) := by
  classical
  obtain ⟨hhom, hcoeff⟩ := rank_weight_basic_invariants N q hq
  exact ⟨hhom, hcoeff,
    RankWeightSupportExchange.rank_weight_support_exchange N q hq,
    RankWeightCoordinateSignature.rank_weight_coordinate_signature N hfull q hq hqone⟩

end CountingMatroid.Analysis.RankWeightCoordinateLorentzian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · proved subset support exchange in RankWeightSupportExchange and assembled the parent certificate through that theorem and the independent RankWeightCoordinateSignature child. Only the general coordinate Hessian bound remains open; the binary and vacuous proofs are preserved in that child.
* 2026-10-09 · blocked · preserved basic invariants and the binary signature proof; discharged the vacuous signature branch below ground size two. Statement-shape searches in pinned Mathlib, Arlib and the project found no independent Brändén–Huh rank-polynomial theorem or coordinate-certificate bridge. The direct generic hyperplane application timed out during definitional equality; the available binary theorem requires ground size two. Proposed the unchanged cited base certificate as prior input, without adding assumptions or child proof debt.
-/
