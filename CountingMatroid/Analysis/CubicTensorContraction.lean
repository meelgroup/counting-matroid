import CountingMatroid.Analysis.QuadraticSignatureHyperplane

set_option autoImplicit false

/-!
The spectral part of cubic directional closure, stated independently of
polynomial calculus. A symmetric nonnegative tensor carries the exchange
support of a homogeneous cubic. The coordinate slices have at most one
positive direction; the remaining obligation is to propagate that bound to
every nonnegative contraction. Arbitrary sums of such slices have no such
closure property without the tensor and support hypotheses.
-/

namespace CountingMatroid.Analysis.CubicTensorContraction

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: Read a cubic tensor's nonzero entries as unordered exponent triples.
TEXLINE: main.tex:340-348 -/
def cubicTensorSupport {σ : Type} [DecidableEq σ] (T : σ → σ → σ → ℚ) :
    Set (σ →₀ ℕ) :=
  {m | ∃ s i j, T s i j ≠ 0 ∧
    m = Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single s 1}

/-- INTERNAL: The polynomial-independent spectral obligation for cubic mixing.
Symmetry, nonnegativity, and exchange support are essential compatibility
hypotheses; the statement does not assert closure of arbitrary sums.
TEXLINE: main.tex:340-348 -/
theorem cubic_tensor_contraction_hyperplane {σ : Type} [Fintype σ] [DecidableEq σ]
    (T : σ → σ → σ → ℚ) (hT : ∀ s i j, 0 ≤ T s i j)
    (hswap : ∀ s i j, T s i j = T i s j)
    (hlast : ∀ s i j, T s i j = T s j i)
    (hex : ∀ x ∈ cubicTensorSupport T, ∀ y ∈ cubicTensorSupport T,
      ∀ i, y i < x i → ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ cubicTensorSupport T)
    (hslice : ∀ s, HasNonpositiveHyperplane
      (Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) •
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))) := by
  classical
  by_cases hzero : ∀ s, d s = 0
  · refine ⟨0, ?_⟩
    intro v _
    simp [hzero]
  by_cases hsingle : ∃ a, ∀ s, s ≠ a → d s = 0
  · obtain ⟨a, ha⟩ := hsingle
    rw [Finset.sum_eq_single a]
    · exact (hslice a).smul (d a : ℝ) (by exact_mod_cast hd a)
    · intro s _ hsa
      simp [ha s hsa]
    · simp
  let : Invertible (2 : ℝ) := invertibleOfNonzero (by norm_num)
  have hreverse (s : σ) (e v : σ → ℝ)
      (he : 0 < Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e) :
      Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) v *
        Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ)) e ≤
      ((Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))).associated e v) ^ 2 := by
    let Q := Matrix.toQuadraticForm' (fun i j => (T s i j : ℝ))
    change Q v * Q e ≤ (Q.associated e v) ^ 2
    have hv : Q.associated e ((Q e) • v - (Q.associated e v) • e) = 0 := by
      simp [QuadraticMap.associated_eq_self_apply, mul_comm]
    have hw := (hslice s).nonpos_of_associated_eq_zero e
      ((Q e) • v - (Q.associated e v) • e) he hv
    have hpolar : QuadraticMap.polar Q v e = 2 * Q.associated e v := by
      have h := congrArg (fun B : LinearMap.BilinForm ℝ (σ → ℝ) => B v e)
        (QuadraticMap.two_nsmul_associated ℝ Q)
      simpa only [LinearMap.smul_apply, nsmul_eq_mul, Nat.cast_ofNat,
        QuadraticMap.polarBilin_apply_apply, QuadraticMap.associated_isSymm ℝ Q v e]
        using h.symm
    have hexp : Q ((Q e) • v - (Q.associated e v) • e) =
        Q e * (Q v * Q e - (Q.associated e v) ^ 2) := by
      rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q,
        QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpolar]
      simp only [QuadraticMap.map_smul, smul_eq_mul]
      ring
    change Q ((Q e) • v - (Q.associated e v) • e) ≤ 0 at hw
    rw [hexp] at hw
    have hprod : Q v * Q e - (Q.associated e v) ^ 2 ≤ 0 :=
      (mul_le_mul_iff_right₀ he).mp (by simpa using hw)
    linarith
  -- Concrete route: each slice is nonpositive on the associated orthogonal
  -- complement of a positive vector (the imported
  -- HasNonpositiveHyperplane.nonpos_of_associated_eq_zero). Tensor symmetry
  -- identifies the slice pairings with coordinates of the contraction.
  -- The proved hreverse above is the resulting local Rayleigh inequality.
  -- Summing its right-hand sides still requires the global spectral step;
  -- the slice hyperplanes need not agree.
  -- BLOCKER: the local-to-global spectral argument using exchange support
  -- to exclude disconnected positive components; it must also handle zero
  -- tensor rows and directions with at least two positive entries.
  sorry

end CountingMatroid.Analysis.CubicTensorContraction

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · proved each slice's reverse Cauchy–Schwarz estimate from its nonpositive hyperplane. Handoff agent2-cubic-tensor-20261009-1 was deferred at the validation deadline; ownership remains local pending settled-boundary revalidation.
* 2026-10-09 · decomposed · stated the tensor-only contraction boundary; proved zero-direction and single-coordinate-direction cases. The general compatible-tensor spectral step remains open.
-/
