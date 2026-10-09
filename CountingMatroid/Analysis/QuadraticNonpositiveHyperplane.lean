import Mathlib.LinearAlgebra.QuadraticForm.Signature
import Mathlib.Data.Real.Basic

set_option autoImplicit false

/-!
A quadratic form is nonpositive on a hyperplane if some real linear
functional has a nonpositive kernel. This property survives linear pullback
and nonnegative scaling. It implies the signature bound, and also gives
nonpositivity on the orthogonal complement of any positive vector.
No property of matroid polynomials is assumed or asserted here.
-/

namespace CountingMatroid.Analysis.QuadraticNonpositiveHyperplane

/-- INTERNAL: A witness for the codimension-at-most-one nonpositive subspace
needed in the quadratic signature argument.
TEXLINE: main.tex:326-348 -/
def HasNonpositiveHyperplane {V : Type} [AddCommGroup V] [Module ℝ V]
    (Q : QuadraticForm ℝ V) : Prop :=
  ∃ l : V →ₗ[ℝ] ℝ, ∀ v, l v = 0 → Q v ≤ 0

/-- INTERNAL: Pulling back a nonpositive hyperplane needs no injectivity,
surjectivity, or sign conditions on the linear map.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.comp {V W : Type}
    [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) (A : W →ₗ[ℝ] V) :
    HasNonpositiveHyperplane (Q.comp A) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l.comp A, fun v hv => hl (A v) hv⟩

/-- INTERNAL: Nonnegative scaling preserves the same nonpositive hyperplane.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.smul {V : Type} [AddCommGroup V] [Module ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (c : ℝ) (hc : 0 ≤ c) : HasNonpositiveHyperplane (c • Q) := by
  obtain ⟨l, hl⟩ := hQ
  exact ⟨l, fun v hv => mul_nonpos_of_nonneg_of_nonpos hc (hl v hv)⟩

/-- INTERNAL: Rank-nullity converts the hyperplane witness to the exact
positive-signature bound used for quadratic descendants.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.sigPos_le_one {V : Type}
    [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q) : sigPos Q ≤ 1 := by
  obtain ⟨l, hl⟩ := hQ
  have hdim := QuadraticForm.sigPos_add_finrank_le_of_nonpos
    (V := LinearMap.ker l) (fun v hv => hl v (LinearMap.mem_ker.mp hv))
  have hnull := l.finrank_range_add_finrank_ker
  have hrange : Module.finrank ℝ (LinearMap.range l) ≤ 1 := by
    simpa using (LinearMap.range l).finrank_le
  omega

/-- INTERNAL: A nonpositive hyperplane forces nonpositivity on the associated
orthogonal complement of every positive vector. This identifies the exact
kernel used in the parent proof without choosing a special hyperplane.
TEXLINE: main.tex:326-348 -/
theorem HasNonpositiveHyperplane.nonpos_of_associated_eq_zero {V : Type}
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    {Q : QuadraticForm ℝ V} (hQ : HasNonpositiveHyperplane Q)
    (e v : V) (he : 0 < Q e) (hv : Q.associated e v = 0) : Q v ≤ 0 := by
  obtain ⟨l, hl⟩ := hQ
  have hle : l e ≠ 0 := by
    intro h
    exact (not_le_of_gt he) (hl e h)
  have hu := hl ((l e) • v - (l v) • e) (by simp [mul_comm])
  have hpolar : QuadraticMap.polar Q v e = 0 := by
    have horth := (QuadraticMap.associated_isOrtho.mp hv).symm
    exact horth.polar_eq_zero
  have hexp : Q ((l e) • v - (l v) • e) =
      (l e) ^ 2 * Q v + (l v) ^ 2 * Q e := by
    rw [sub_eq_add_neg, ← neg_smul, QuadraticMap.map_add Q ((l e) • v) (-(l v) • e),
      QuadraticMap.polar_smul_left, QuadraticMap.polar_smul_right, hpolar]
    simp only [QuadraticMap.map_smul, smul_eq_mul]
    ring
  rw [hexp] at hu
  have hterm : 0 ≤ (l v) ^ 2 * Q e := mul_nonneg (sq_nonneg _) he.le
  have hsq : 0 < (l e) ^ 2 := sq_pos_of_ne_zero hle
  nlinarith

end CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
