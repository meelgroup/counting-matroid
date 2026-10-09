import CountingMatroid.Analysis.SquarefreeCoordinateHessian
import Mathlib.Combinatorics.Matroid.Rank.ENat

set_option autoImplicit false

/-! The matroid part of the coordinate-signature calculation, separated from
the polynomial differentiation identity. The residual matrix uses ranks of
the selected set and its one- and two-element extensions. Its nonpositive
hyperplane is explicit; the remaining obligation is the sign of the matrix
on that hyperplane. -/

namespace CountingMatroid.Analysis.RankWeightResidualSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane SquarefreeCoordinateHessian

/-- INTERNAL: After fixing the selected labels, the residual rank-weight
matrix has a nonpositive hyperplane. The witness normalizes the homogenizer
coordinate against the weighted sum of the remaining label coordinates.
TEXLINE: main.tex:334-348 -/
theorem rank_weight_residual_signature {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (S : Finset α) (k : ℕ) (hsize : S.card + k + 2 = Fintype.card α) :
    HasNonpositiveHyperplane
      (squarefreeResidualHessian
        (fun A : Finset α => (q ^ (N.eRk (A : Set α)).toNat)⁻¹)
        S k).toQuadraticForm' := by
  classical
  let w : Finset α → ℝ := fun A => ((q ^ (N.eRk (A : Set α)).toNat)⁻¹ : ℚ)
  have hw : ∀ A, 0 < w A := by
    intro A
    dsimp only [w]
    exact_mod_cast inv_pos.mpr (pow_pos hq (N.eRk (A : Set α)).toNat)
  refine ⟨((k + 2 : ℝ) * w S) • LinearMap.proj none +
    ∑ a ∈ Finset.univ \ S, w (insert a S) • LinearMap.proj (some a), ?_⟩
  intro v hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.proj_apply, smul_eq_mul] at hv
  simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
    Matrix.toLinearMap₂'_apply]
  -- BLOCKER: prove this finite quadratic sum nonpositive using the rank
  -- increments relative to S. Normalize y_a = w(insert a S) / w S * v(some a).
  -- Elements in closure S have increment zero. On the others, equality of
  -- closure(insert a S) partitions the elements into parallel classes of N/S.
  -- The normalized mixed coefficient is q within a class and 1 across classes.
  -- Writing Y = sum y_a and m = k+2, the normalized quadratic is
  --   m*(m-1)*z^2 + 2*(m-1)*z*Y + Y^2
  --     - sum(loop a) y_a^2 - q*sum(nonloop a) y_a^2
  --     - (1-q)*sum(class C) (sum(a in C) y_a)^2.
  -- The hyperplane hv is m*z+Y=0. The first three terms are -Y^2/m;
  -- every remaining term is nonpositive since 0<q<=1.
  sorry

end CountingMatroid.Analysis.RankWeightResidualSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · chose the explicit weighted hyperplane, proved positivity of every rank weight, and expanded the matrix quadratic. The remaining sign calculation requires the parallel-class decomposition of rank increments after contracting the selected set.
-/
