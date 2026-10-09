import CountingMatroid.Analysis.BinaryRankWeightSignature

set_option autoImplicit false

/-!
The original-variable mixed-derivative prerequisite for the rank-weight
signature theorem. Linear substitution and scalar closure are proved in the
parent's other support modules. The empty direction list is handled by
the two-element rank-weight calculation, and an identically zero head
direction gives the zero quadratic form. The remaining nonempty-list case
is the cited Brändén–Huh input: the pinned libraries contain no applicable
Lorentzian base or closure theorem. Separate hyperplane bounds for summands
do not establish the common-source compatibility needed here.
-/

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- PAPER: main.tex:334-348
The original-variable hyperplane consequence of the cited Lorentzian base
and closure results,
for the common matroid polynomial after exactly ground-size minus two
nonnegative directional derivatives. The fold is the parent's proved normal
form, with the last derivative at the head of the list.
BORROWED: Bränden–Huh, Lorentzian polynomials (2020), Theorems 4.10,
2.10 and Corollary 2.11 supply the Lorentzian base and closure input. -/
theorem mixed_directional_rank_weight_nonpositive_hyperplane {α : Type}
    [Fintype α] [DecidableEq α] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (ds : List (Option α → ℚ))
    (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s)
    (hlength : ds.length + 2 = Fintype.card α) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    let g := ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j g)) : ℚ) : ℝ))) := by
  induction ds with
  | nil =>
    exact BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
      N q hq hqone (by simpa using hlength.symm)
  | cons d ds ih =>
    by_cases hd : ∀ s, d s = 0
    · dsimp only
      simp only [List.foldr_cons, hd, map_zero, zero_mul, Finset.sum_const_zero,
        Rat.cast_zero]
      refine ⟨0, ?_⟩
      intro v hv
      change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v ≤ 0
      rw [map_zero]
      simp
    · -- BLOCKER: library name not found. Searches of pinned Mathlib and Arlib
      -- by matroid rank-weight polynomial, Lorentzian/log-concave closure,
      -- Hessian and positive signature found no applicable base/closure result.
      -- The cited input is main.tex:334-348, BH2020 Theorems 4.10, 2.10
      -- and Corollary 2.11. Propose this exact consequence as prior input;
      -- no field of Prior has been added or assumed here.
      -- A stdin induction attempt failed on ds.length + 2 = |α|:
      -- this branch instead has ds.length + 3 = |α|, so the tail is cubic.
      -- Focused arithmetic probes also prove |α| ≠ 2 here, ruling out
      -- binary_tutte_nonpositive_hyperplane. Separate hyperplanes for the
      -- coordinate derivative Hessians cannot be added into a shared one.
      -- RankWeightQuadraticSignature imports and uses this theorem, so its
      -- general signature declaration cannot be imported as a proof of it.
      sorry

end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · blocked · proved the identically zero head-direction branch; searched pinned Mathlib and Arlib by Lorentzian/log-concave closure, matroid polynomial Hessian and positive signature without finding the cited input. Stdin probes verified the tail-length and binary-cardinality mismatches. Proposed this unchanged Brändén–Huh consequence as prior input; no new helper, assumption or import was introduced.
* 2026-10-09 · open · stated the exact original-variable mixed-directional prerequisite and proved its empty-direction branch using BinaryRankWeightSignature; direct list induction cannot use its quadratic induction hypothesis on the cubic tail.
-/
