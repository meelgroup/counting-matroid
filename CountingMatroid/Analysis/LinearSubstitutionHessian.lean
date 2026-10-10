import CountingMatroid.Analysis.LinearPolynomialChainRule
import Mathlib.LinearAlgebra.QuadraticForm.Basic
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
Linear substitutions pull back the Hessian quadratic form by their transpose
on variable values. This identity holds for arbitrary rational polynomials,
including zero substitution columns and identified variables. It provides
the algebraic part of the substitution closure in the quadratic argument.
-/

namespace CountingMatroid.Analysis.LinearSubstitutionHessian

open scoped BigOperators

/-- INTERNAL: A linear substitution without a constant term preserves the
constant coefficient.
TEXLINE: main.tex:326-348 -/
theorem constantCoeff_linear_aeval {σ τ : Type} [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.constantCoeff
      (MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p) =
    MvPolynomial.constantCoeff p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p s hp => simp [hp]

/-- INTERNAL: The Hessian transforms by matrix congruence under a linear
substitution; this is a coefficient identity before casting to the reals.
TEXLINE: main.tex:326-348 -/
theorem linear_aeval_hessian {σ τ : Type} [Fintype σ] [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (i j : τ) :
    MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) =
    ∑ s, ∑ t, a s i *
      MvPolynomial.constantCoeff (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) *
        a t j := by
  classical
  rw [LinearPolynomialChainRule.linear_aeval_pderiv,
    LinearPolynomialChainRule.linear_aeval_pderiv,
    constantCoeff_linear_aeval]
  simp only [map_sum, MvPolynomial.pderiv_C_mul, map_mul, MvPolynomial.constantCoeff_C]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  ring

/-- INTERNAL: Matrix congruence is exactly linear pullback of the associated
quadratic form, including rectangular and singular substitution matrices.
TEXLINE: main.tex:326-348 -/
theorem quadraticForm_congruence {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (H : Matrix σ σ ℝ) (A : Matrix σ τ ℝ) :
    (A.transpose * H * A).toQuadraticForm' = H.toQuadraticForm'.comp A.toLin' := by
  have hB : Matrix.toLinearMap₂' ℝ (A.transpose * H * A) =
      (Matrix.toLinearMap₂' ℝ H).compl₁₂ A.toLin' A.toLin' := by
    apply (LinearMap.toMatrix₂' ℝ).injective
    simp
  simpa only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_comp_same] using
    congrArg LinearMap.BilinMap.toQuadraticMap hB

/-- INTERNAL: The rational polynomial Hessian, cast to the reals, pulls back
by the real linear map of variable values under substitution.
TEXLINE: main.tex:326-348 -/
theorem linear_aeval_hessian_quadraticForm {σ τ : Type} [Fintype σ] [Fintype τ]
    [DecidableEq σ] [DecidableEq τ] (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) :
    Matrix.toQuadraticForm' (fun i j => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) : ℚ) : ℝ)) =
    (Matrix.toQuadraticForm' (fun s t => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ))).comp
        (Matrix.toLin' (fun s t => (a s t : ℝ))) := by
  let A : Matrix σ τ ℝ := fun s t => (a s t : ℝ)
  let H : Matrix σ σ ℝ := fun s t => ((MvPolynomial.constantCoeff
    (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ)
  have hmat : ((fun i j => ((MvPolynomial.constantCoeff
      (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (MvPolynomial.aeval
          (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p))) : ℚ) : ℝ)) : Matrix τ τ ℝ) =
      A.transpose * H * A := by
    ext i j
    change _ = ∑ t, (∑ s, (a s i : ℝ) *
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv s (MvPolynomial.pderiv t p)) : ℚ) : ℝ)) *
        (a t j : ℝ)
    rw [linear_aeval_hessian]
    simp only [Rat.cast_sum, Rat.cast_mul, Finset.sum_mul]
    rw [Finset.sum_comm]
  rw [hmat]
  exact quadraticForm_congruence H A

end CountingMatroid.Analysis.LinearSubstitutionHessian
