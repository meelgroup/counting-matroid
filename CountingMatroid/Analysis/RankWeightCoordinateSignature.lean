import CountingMatroid.Analysis.LorentzianDirectionalSignature
import CountingMatroid.Analysis.BinaryRankWeightSignature
import CountingMatroid.Analysis.RankWeightSupportExchange
import CountingMatroid.Analysis.SquarefreeCoordinateHessian
import CountingMatroid.Analysis.RankWeightResidualSignature

set_option autoImplicit false

/-! The matroid-specific coordinate Hessian bound, independently of the
subset support exchange argument. Ground sizes at most two and derivatives
beginning with two identical labels are verified. The general bound is reduced
to a squarefree-polynomial Hessian identity and a matroid residual-matrix
hyperplane bound; both imported obligations remain open. The paper instead
invokes Brändén–Huh (2020), Theorem 4.10, Theorem 2.10 and Corollary 2.11
at main.tex:334-348 without proving them.

No independent rank-weight Lorentzian or Hessian-signature theorem was found
in the pinned Mathlib or Arlib sources. The downstream
`RankWeightCoordinateLorentzian.rank_weight_coordinate_lorentzian` cannot
supply the missing input: it constructs its coordinate-signature field using
this theorem. The generic coordinate and directional certificate APIs require
that field as a hypothesis; they do not establish the matroid-specific bound.
The new residual-matrix reduction does not use either certificate API.
-/

namespace CountingMatroid.Analysis.RankWeightCoordinateSignature

open scoped BigOperators
open LorentzianDirectionalSignature
open RankWeightSupportExchange

/-- INTERNAL: Coordinate derivatives of a monomial remain a monomial with
coordinatewise smaller exponents, including the zero coefficient case. -/
theorem coordinate_derivative_monomial {σ : Type}
    (xs : List σ) (m : σ →₀ ℕ) (c : ℚ) :
    ∃ e : σ →₀ ℕ, ∃ b : ℚ, e ≤ m ∧
      xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (MvPolynomial.monomial m c) = MvPolynomial.monomial e b := by
  induction xs with
  | nil => exact ⟨m, c, le_rfl, rfl⟩
  | cons s xs ih =>
    obtain ⟨e, b, he, hpoly⟩ := ih
    refine ⟨e - Finsupp.single s 1, b * e s, ?_, ?_⟩
    · exact le_trans tsub_le_self he
    · simp only [List.foldr_cons, hpoly, MvPolynomial.pderiv_monomial]

/-- INTERNAL: Iterated coordinate derivatives distribute over finite sums. -/
theorem coordinate_derivative_sum {σ β : Type} (xs : List σ)
    (S : Finset β) (f : β → MvPolynomial σ ℚ) :
    xs.foldr (fun s p => MvPolynomial.pderiv s p) (∑ b ∈ S, f b) =
      ∑ b ∈ S, xs.foldr (fun s p => MvPolynomial.pderiv s p) (f b) := by
  induction xs with
  | nil => rfl
  | cons s xs ih => simp only [List.foldr_cons, ih, map_sum]

/-- INTERNAL: Squarefree label exponents annihilate any derivative beginning
with two identical label coordinates, regardless of its remaining tail.
TEXLINE: main.tex:334-339 -/
theorem rank_weight_repeated_label_zero {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (a : α) (ys : List (Option α)) :
    (some a :: some a :: ys).foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ A : Finset α,
        MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ b ∈ A, MvPolynomial.X (some b)) = 0 := by
  classical
  rw [coordinate_derivative_sum]
  apply Finset.sum_eq_zero
  intro A _
  rw [rank_weight_term_monomial]
  obtain ⟨e, c, he, hpoly⟩ := coordinate_derivative_monomial ys
    (subsetExponent A) ((q ^ (N.eRk (A : Set α)).toNat)⁻¹)
  have heone : e (some a) ≤ 1 := by
    have hbound := he (some a)
    rw [subsetExponent_some] at hbound
    split_ifs at hbound <;> omega
  simp only [List.foldr_cons, hpoly, MvPolynomial.pderiv_monomial,
    Finsupp.tsub_apply, Finsupp.single_eq_same]
  have hz : e (some a) - 1 = 0 := by omega
  simp [hz]

/-- PAPER: main.tex:334-348
Every quadratic coordinate derivative of the homogenized rank-weight
polynomial has at most one positive Hessian eigenvalue.
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Theorem 4.10,
with partial derivative closure (Theorem 2.10 and Corollary 2.11) and the
defining quadratic signature property. -/
theorem rank_weight_coordinate_signature {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (xs : List (Option α)) (hlength : xs.length + 2 = Fintype.card α) :
    sigPos (constantHessianForm
      (xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (∑ A : Finset α,
          MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
            MvPolynomial.X none ^ (Fintype.card α - A.card) *
              ∏ a ∈ A, MvPolynomial.X (some a)))) ≤ 1 := by
  classical
  by_cases hrepeat : ∃ a ys, xs = some a :: some a :: ys
  · obtain ⟨a, ys, rfl⟩ := hrepeat
    rw [rank_weight_repeated_label_zero N q a ys]
    apply QuadraticNonpositiveHyperplane.HasNonpositiveHyperplane.sigPos_le_one
    refine ⟨0, ?_⟩
    intro v _
    simp only [constantHessianForm, map_zero, Rat.cast_zero,
      Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply]
    change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v ≤ 0
    rw [map_zero]
    simp
  by_cases hsmall : Fintype.card α < 2
  · omega
  · by_cases htwo : Fintype.card α = 2
    · have hnil : xs = [] := by
        apply List.eq_nil_iff_length_eq_zero.mpr
        omega
      subst xs
      exact (BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
        N q hq hqone htwo).sigPos_le_one
    · cases xs with
      | nil => simp only [List.length_nil] at hlength; omega
      | cons s xs =>
        simp only [List.foldr_cons]
        obtain ⟨S, k, c, hc, hsize, hform⟩ :=
          SquarefreeCoordinateHessian.squarefree_coordinate_hessian
            (fun A : Finset α => (q ^ (N.eRk (A : Set α)).toNat)⁻¹)
            (s :: xs) hlength
        have hsignature :=
          (RankWeightResidualSignature.rank_weight_residual_signature
            N hfull q hq hqone S k hsize).smul c hc
        rw [← hform] at hsignature
        exact hsignature.sigPos_le_one

end CountingMatroid.Analysis.RankWeightCoordinateSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · deferred handoff · the scheduler retained these children because CubicTensorContraction has an active writer in their build closure. Continued in the polynomial child: derivative commutation and excessive-count monomial annihilation are proved, closing every repeated-label normal-form branch. The two remaining boundaries are distinct-label factorial coefficient extraction and the residual matroid matrix sign bound.
* 2026-10-09 · decomposed · replaced the general local hole by the explicit squarefree-coordinate Hessian normal form and residual rank-weight matrix hyperplane bound. This replaces the cited Lorentzian-certificate route by polynomial coefficient extraction and a parallel-class square decomposition. Both substantial child obligations remain open; all earlier binary, vacuous, and repeated-label proofs and imports are preserved.
* 2026-10-09 · library dependency blocked · rechecked the target and its named dependencies; the file elaborates with its existing open signature warning. Searched 9,774 Mathlib and 385 Arlib Lean sources for Lorentzian, M-convex, Tutte/rank-generating, log-concavity, and matroid/polynomial/Hessian statements; found no applicable borrowed result. A stdin coordinate-certificate application exposes the missing certificate, and the downstream certificate explicitly calls this theorem. Proposed only the unchanged borrowed coordinate-signature statement as Prior input; preserved every proof and added no helper debt.
* 2026-10-09 · partial · proved that iterated coordinate derivatives of a monomial decrease all exponents; consequently two repeated leading label derivatives annihilate the rank-weight polynomial after any tail. This closes an additional signature branch, without using positivity, full ground, or a Lorentzian assumption. The live handoff was deferred because LorentzianDirectionalSignature still had an active writer.
* 2026-10-09 · open · separated the general coordinate signature from the independently proved subset support description; preserved the binary and vacuous cases. The nonempty-list route requires a degree-three derivative invariant or a contracted-rank-polynomial normal form, not the available two-element certificate.
-/
