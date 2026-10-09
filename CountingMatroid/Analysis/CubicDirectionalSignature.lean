import CountingMatroid.Analysis.QuadraticSignatureHyperplane
import CountingMatroid.Analysis.CubicThirdDerivativeSupport
import CountingMatroid.Analysis.CubicTensorContraction
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false

/-!
The cubic step in directional Lorentzian closure. This isolates the spectral
obligation from support preservation: the constant Hessians of the coordinate
derivatives of a cubic arise from one symmetric nonnegative cubic tensor.
The polynomial support is identified with the tensor's unordered triples by
`CubicThirdDerivativeSupport`. The directional signature then follows from
the tensor contraction boundary in `CubicTensorContraction`, whose general
spectral proof remains open. No closure of arbitrary sums is asserted.
-/

namespace CountingMatroid.Analysis.CubicDirectionalSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane QuadraticSignatureHyperplane

set_option backward.isDefEq.respectTransparency false in
/-- INTERNAL: Formal differentiation identifies a directional Hessian with
its nonnegative weighted coordinate Hessians; no spectral closure is used.
TEXLINE: main.tex:340-348 -/
theorem directional_hessian_eq_sum {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (d : σ → ℚ) :
    Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ)) =
    ∑ s, (d s : ℝ) • Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ)) := by
  have hm : (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ)) =
      ∑ s, (d s : ℝ) • (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ)) := by
    ext i j
    simp
  rw [hm]
  simp only [Matrix.toQuadraticForm', map_sum, map_smul,
    LinearMap.BilinMap.toQuadraticMap_sum, LinearMap.BilinMap.toQuadraticMap_smul]

/-- INTERNAL: The cubic mixing step suffices for directional closure at every
degree, by first taking coordinate derivatives down to degree three.
TEXLINE: main.tex:340-348 -/
theorem cubic_directional_signature {σ : Type} [Fintype σ] [DecidableEq σ]
    (p : MvPolynomial σ ℚ) (hhom : p.IsHomogeneous 3)
    (hp : ∀ m, 0 ≤ p.coeff m)
    (hex : ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support)
    (hsig : ∀ s, sigPos (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ))) ≤ 1)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    sigPos (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
        (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p))) : ℚ) : ℝ))) ≤ 1 := by
  classical
  let T : σ → σ → σ → ℚ := fun s i j =>
    MvPolynomial.constantCoeff (MvPolynomial.pderiv i
      (MvPolynomial.pderiv j (MvPolynomial.pderiv s p)))
  have hderiv (f : MvPolynomial σ ℚ) (hf : ∀ m, 0 ≤ f.coeff m)
      (s : σ) (m : σ →₀ ℕ) : 0 ≤ (MvPolynomial.pderiv s f).coeff m := by
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hf _) (by positivity)
  have hT : ∀ s i j, 0 ≤ T s i j := by
    intro s i j
    exact hderiv _ (hderiv _ (hderiv p hp s) j) i 0
  have hswap : ∀ s i j, T s i j = T i s j := by
    intro s i j
    simp only [T, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
      zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
    by_cases hsi : s = i <;> by_cases hsj : s = j <;> by_cases hij : i = j <;>
      simp_all [Finsupp.add_apply, add_comm, add_left_comm, mul_comm, mul_left_comm]
  have hlast : ∀ s i j, T s i j = T s j i := by
    intro s i j
    simp only [T, MvPolynomial.constantCoeff_eq, MvPolynomial.coeff_pderiv,
      zero_add, Finsupp.zero_apply, Nat.cast_zero, zero_add, mul_one]
    by_cases hij : i = j
    · subst j
      rfl
    · simp [Finsupp.add_apply, hij, Ne.symm hij, add_comm,
        mul_comm, mul_left_comm]
  have hsupp (m : σ →₀ ℕ) :
      m ∈ CubicTensorContraction.cubicTensorSupport T ↔ m ∈ p.support :=
    (CubicThirdDerivativeSupport.cubic_third_derivative_support p hhom m).symm
  have hTex : ∀ x ∈ CubicTensorContraction.cubicTensorSupport T,
      ∀ y ∈ CubicTensorContraction.cubicTensorSupport T, ∀ i, y i < x i →
      ∃ j, x j < y j ∧ x - Finsupp.single i 1 + Finsupp.single j 1 ∈
        CubicTensorContraction.cubicTensorSupport T := by
    intro x hx y hy i hi
    obtain ⟨j, hj, hm⟩ := hex x ((hsupp x).mp hx) y ((hsupp y).mp hy) i hi
    exact ⟨j, hj, (hsupp _).mpr hm⟩
  have hplanes : ∀ s, HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i
        (MvPolynomial.pderiv j (MvPolynomial.pderiv s p))) : ℚ) : ℝ))) :=
    fun s => hasNonpositiveHyperplane_of_sigPos_le_one _ (hsig s)
  rw [directional_hessian_eq_sum]
  apply HasNonpositiveHyperplane.sigPos_le_one
  exact CubicTensorContraction.cubic_tensor_contraction_hyperplane T hT hswap hlast
    hTex hplanes d hd

end CountingMatroid.Analysis.CubicDirectionalSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · deferred handoff · fresh request agent2-cubic-tensor-20261009-2 was also deferred at the build-validation deadline. The checked decomposition and the single tensor spectral obligation are preserved; neither child has transferred ownership.
* 2026-10-09 · deferred handoff · request agent2-cubic-tensor-20261009-1 reached the validation deadline at build stage; ownership retained. The parent elaborates, the support bridge is proved, and the tensor child additionally proves the local reverse Cauchy–Schwarz estimate; the general contraction bound remains open.
* 2026-10-09 · decomposed · proved tensor nonnegativity, symmetry, and transfer of exchange support; the target now uses the proved cubic-support bridge and the tensor-only contraction child. The spectral proof debt remains in CubicTensorContraction.cubic_tensor_contraction_hyperplane pending live handoff.
-/
