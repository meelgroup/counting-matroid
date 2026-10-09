import Mathlib.Algebra.MvPolynomial.PDeriv

set_option autoImplicit false

/-!
Formal polynomial calculus for moving derivatives before linear substitutions.
These identities do not assert Lorentzianity or a signature bound.
-/

namespace CountingMatroid.Analysis.LinearPolynomialChainRule

open scoped BigOperators

/-- INTERNAL: The chain rule for a linear substitution, in the exact algebraic
form needed to normalize a descendant derivation.
TEXLINE: main.tex:326-348 -/
theorem linear_aeval_pderiv {σ τ : Type} [Fintype σ] [Fintype τ]
    (a : σ → τ → ℚ) (p : MvPolynomial σ ℚ) (t : τ) :
    MvPolynomial.pderiv t
      (MvPolynomial.aeval (fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u) p) =
    MvPolynomial.aeval (fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u)
      (∑ s, MvPolynomial.C (a s t) * MvPolynomial.pderiv s p) := by
  classical
  let L := fun s => ∑ u, MvPolynomial.C (a s u) * MvPolynomial.X u
  have hL (s : σ) : MvPolynomial.pderiv t (L s) = MvPolynomial.C (a s t) := by
    simp [L, MvPolynomial.pderiv_X, Pi.single_apply]
  change MvPolynomial.pderiv t (MvPolynomial.aeval L p) =
    MvPolynomial.aeval L (∑ s, MvPolynomial.C (a s t) * MvPolynomial.pderiv s p)
  induction p using MvPolynomial.induction_on with
  | C c => simp
  | add p q hp hq => simp [hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p j hp =>
    simp only [map_mul, MvPolynomial.aeval_X, MvPolynomial.pderiv_mul, hp, hL,
      MvPolynomial.pderiv_X, Pi.single_apply, mul_add, Finset.sum_add_distrib]
    simp only [map_add, map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq]
    simp only [Finset.sum_mul]
    congr 1
    · apply Finset.sum_congr rfl
      intro s _
      rw [MvPolynomial.aeval_X]
      exact mul_assoc _ _ _
    · simp [mul_comm]

/-- INTERNAL: Consecutive linear substitutions compose by matrix multiplication.
TEXLINE: main.tex:326-348 -/
theorem linear_aeval_comp {σ τ υ : Type} [Fintype τ] [Fintype υ]
    (a : σ → τ → ℚ) (b : τ → υ → ℚ) (p : MvPolynomial σ ℚ) :
    MvPolynomial.aeval (fun t => ∑ u, MvPolynomial.C (b t u) * MvPolynomial.X u)
      (MvPolynomial.aeval (fun s => ∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t) p) =
    MvPolynomial.aeval
      (fun s => ∑ u, MvPolynomial.C (∑ t, a s t * b t u) * MvPolynomial.X u) p := by
  rw [MvPolynomial.comp_aeval_apply]
  suffices h : (fun s =>
      MvPolynomial.aeval (fun t => ∑ u, MvPolynomial.C (b t u) * MvPolynomial.X u)
        (∑ t, MvPolynomial.C (a s t) * MvPolynomial.X t)) =
      (fun s => ∑ u, MvPolynomial.C (∑ t, a s t * b t u) * MvPolynomial.X u) by
    rw [h]
  funext s
  simp only [map_sum, map_mul, MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq,
    MvPolynomial.aeval_X, Finset.mul_sum, map_sum, Finset.sum_mul,
    map_mul, mul_assoc]
  exact Finset.sum_comm

end CountingMatroid.Analysis.LinearPolynomialChainRule

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · established the formal chain rule for linear polynomial substitution and the matrix-composition identity; both are used by RankWeightQuadraticSignature.descendant_directional_normal_form.
-/
