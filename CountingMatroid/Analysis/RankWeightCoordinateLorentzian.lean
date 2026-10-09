import CountingMatroid.Analysis.LorentzianDirectionalSignature
import CountingMatroid.Analysis.BinaryRankWeightSignature

set_option autoImplicit false

/-!
The matroid-specific coordinate certificate needed by the general Lorentzian
directional-closure theorem. Homogeneity and coefficient nonnegativity are
proved directly. Support exchange and the coordinate quadratic signatures
remain open. The coordinate-signature field is verified for ground size at most
two (vacuously below two). Statement-shape searches found no corresponding
Brändén–Huh theorem or Lorentzian-to-coordinate bridge in pinned Mathlib or
Arlib. No directional-derivative conclusion is assumed here.
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
supplies Lorentzianity, hence its coordinate quadratic signatures and support
exchange property. -/
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
  refine ⟨hhom, hcoeff, ?_, ?_⟩
  · -- BLOCKER (library name not found): no Lorentzian/M-convex support
    -- theorem for matroid rank-generating polynomials was found in pinned
    -- Mathlib or Arlib. The local direct route requires identifying each support exponent
    -- with a subset A (label exponents 0/1, homogenizing exponent |α|-|A|).
    -- The exchange witness then inserts/removes one label, or transfers a
    -- label to/from none. Expanding polynomial support with simp alone
    -- does not recover this subset representation.
    sorry
  · intro xs hlength
    by_cases hsmall : Fintype.card α < 2
    · omega
    · by_cases htwo : Fintype.card α = 2
      · have hnil : xs = [] := by
          apply List.eq_nil_iff_length_eq_zero.mpr
          omega
        subst xs
        exact (BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
          N q hq hqone htwo).sigPos_le_one
      · -- BLOCKER (library name not found): the binary calculation handles only |α|=2. For longer
        -- coordinate lists, deleting the differentiated labels contracts the
        -- matroid; differentiating none contributes falling-factorial weights.
        -- Rank submodularity gives pairwise coefficient bounds, but those
        -- alone do not prove a common nonpositive hyperplane for all remaining
        -- labels. The missing matroid-specific input is the coordinate Hessian
        -- signature part of BH2020 Theorem 4.10, not directional closure.
        -- Searches included Lorentzian/M-convex support, rank-generating/Tutte
        -- polynomials, matroid polynomial Hessians, and complete log-concavity
        -- in pinned Mathlib and Arlib. No applicable declaration was found.
        -- Project signature consequences depend on this file and cannot supply
        -- the missing base certificate without an import cycle.
        sorry

end CountingMatroid.Analysis.RankWeightCoordinateLorentzian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · blocked · preserved basic invariants and the binary signature proof; discharged the vacuous signature branch below ground size two. Statement-shape searches in pinned Mathlib, Arlib and the project found no independent Brändén–Huh rank-polynomial theorem or coordinate-certificate bridge. The direct generic hyperplane application timed out during definitional equality; the available binary theorem requires ground size two. Proposed the unchanged cited base certificate as prior input, without adding assumptions or child proof debt.
-/
