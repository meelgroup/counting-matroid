import CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

set_option autoImplicit false

/-!
Convert an at-most-one-positive signature bound to the linear-functional
witness used by the rank-weight analysis. Mathlib diagonalizes the quadratic
form; deleting its sole positive square leaves a nonpositive kernel.
This module establishes no signature bound for matroid polynomials.
-/

namespace CountingMatroid.Analysis.QuadraticSignatureHyperplane

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: The positive-signature conclusion of the cited quadratic
Lorentzian theory supplies the hyperplane witness used by this development.
Uses `QuadraticForm.equivalent_weightedSumSquares` and
`QuadraticForm.sigPos_of_equiv_weightedSumSquares` from Mathlib.
TEXLINE: main.tex:340-348 -/
theorem hasNonpositiveHyperplane_of_sigPos_le_one {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (Q : QuadraticForm ℝ V) (hQ : sigPos Q ≤ 1) :
    HasNonpositiveHyperplane Q := by
  classical
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  obtain ⟨w, hw⟩ := Q.equivalent_weightedSumSquares
  have hcount : {i | 0 < w i}.ncard ≤ 1 := by
    rwa [QuadraticForm.sigPos_of_equiv_weightedSumSquares hw] at hQ
  have hdiag : HasNonpositiveHyperplane (QuadraticMap.weightedSumSquares ℝ w) := by
    by_cases hp : ∃ i, 0 < w i
    · obtain ⟨i, hi⟩ := hp
      refine ⟨LinearMap.proj i, ?_⟩
      intro v hv
      change v i = 0 at hv
      rw [QuadraticMap.weightedSumSquares_apply]
      apply Finset.sum_nonpos
      intro j _
      by_cases hji : j = i
      · subst j
        simp [hv]
      · have hj : w j ≤ 0 := by
          by_contra hn
          exact hji (((Set.ncard_le_one (Set.toFinite _)).mp hcount)
            j (lt_of_not_ge hn) i hi)
        exact mul_nonpos_of_nonpos_of_nonneg hj (mul_self_nonneg _)
    · refine ⟨0, ?_⟩
      intro v _
      rw [QuadraticMap.weightedSumSquares_apply]
      apply Finset.sum_nonpos
      intro j _
      exact mul_nonpos_of_nonpos_of_nonneg (le_of_not_gt (fun hj => hp ⟨j, hj⟩))
        (mul_self_nonneg _)
  obtain ⟨e⟩ := hw
  obtain ⟨l, hl⟩ := hdiag
  refine ⟨l.comp e.toLinearEquiv.toLinearMap, ?_⟩
  intro v hv
  rw [← e.map_app v]
  exact hl (e v) hv

end CountingMatroid.Analysis.QuadraticSignatureHyperplane
