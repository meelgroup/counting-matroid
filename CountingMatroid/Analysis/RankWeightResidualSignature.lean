import CountingMatroid.Analysis.SquarefreeCoordinateHessian
import Mathlib.Combinatorics.Matroid.Rank.ENat
import CountingMatroid.Analysis.ClosureClassQuadraticBound
import CountingMatroid.Analysis.RankWeightClosurePair

set_option autoImplicit false

/-! The matroid part of the coordinate-signature calculation, separated from
the polynomial differentiation identity. The residual matrix uses ranks of
the selected set and its one- and two-element extensions. Its nonpositive
hyperplane is explicit. Rank increments identify parallel closure classes,
and label and class Cauchy–Schwarz estimates prove the matrix nonpositive
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
  let T : Finset α := Finset.univ \ S
  have hcard : T.card = k + 2 := by
    have hc : T.card = Fintype.card α - S.card := by
      simp [T, Finset.card_sdiff]
    omega
  let f : α → Set α := fun a => N.closure (insert a (S : Set α))
  let P : α → Prop := fun a => a ∉ N.closure (S : Set α)
  have hpair (a b : α) :
      w S * (if a = b then 0 else w (insert a (insert b S))) =
        (if a = b then 0 else if P a ∧ P b ∧ f a = f b then (q : ℝ) else 1) *
          w (insert a S) * w (insert b S) := by
    by_cases hab : a = b
    · simp [hab]
    · have hr := RankWeightClosurePair.rank_weight_closure_pair
        N hfull (S : Set α) q hq a b
      have hr' : w S * w (insert a (insert b S)) =
          (if a ∉ N.closure (S : Set α) ∧ b ∉ N.closure (S : Set α) ∧
            N.closure (insert a (S : Set α)) = N.closure (insert b (S : Set α))
          then (q : ℝ) else 1) * w (insert a S) * w (insert b S) := by
        dsimp only [w]
        simp only [Finset.coe_insert]
        rw [mul_comm]
        have hrReal := congrArg (fun t : ℚ => (t : ℝ)) hr
        simpa only [Rat.cast_mul, apply_ite, Rat.cast_one] using hrReal
      rw [if_neg hab, if_neg hab]
      exact hr'
  refine ⟨((k + 2 : ℝ) * w S) • LinearMap.proj none +
    ∑ a ∈ T, w (insert a S) • LinearMap.proj (some a), ?_⟩
  intro v hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, LinearMap.sum_apply,
    LinearMap.proj_apply, smul_eq_mul] at hv
  let y : α → ℝ := fun a => w (insert a S) * v (some a)
  let Y : ℝ := ∑ a ∈ T, y a
  let B : ℝ := ∑ a ∈ T, ∑ b ∈ T,
    v (some a) * v (some b) * (if a = b then 0 else w (insert a (insert b S)))
  have hB : w S * B = ∑ a ∈ T, ∑ b ∈ T,
      (if a = b then 0 else if P a ∧ P b ∧ f a = f b then (q : ℝ) else 1) * y a * y b := by
    dsimp only [B]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    calc
      _ = (w S * (if a = b then 0 else w (insert a (insert b S)))) *
          v (some a) * v (some b) := by ring
      _ = _ := by rw [hpair]; dsimp only [y]; ring
  have hbound := ClosureClassQuadraticBound.parallel_class_quadratic_bound
    T f P (q : ℝ) (by exact_mod_cast hq.le) (by exact_mod_cast hqone) y
  rw [hcard, ← hB] at hbound
  simp only [Nat.cast_add, Nat.cast_ofNat] at hbound
  change (k + 2 : ℝ) * (w S * B) ≤ ((k + 2 : ℝ) - 1) * Y ^ 2 at hbound
  have sumT (g : α → ℝ) :
      (∑ a : α, if a ∈ S then 0 else g a) = ∑ a ∈ T, g a := by
    symm
    apply Finset.sum_subset_zero_on_sdiff (Finset.sdiff_subset)
    · intro a ha
      have haS : a ∈ S := by simpa [T] using ha
      simp [haS]
    · intro a ha
      have haS : a ∉ S := (Finset.mem_sdiff.mp ha).2
      simp [haS]
  have hquad : (squarefreeResidualHessian
      (fun A : Finset α => (q ^ (N.eRk (A : Set α)).toNat)⁻¹) S k).toQuadraticForm' v =
      (k + 2 : ℝ) * (k + 1 : ℝ) * w S * (v none) ^ 2 +
        2 * (k + 1 : ℝ) * v none * Y + B := by
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply, smul_eq_mul, Fintype.sum_option]
    change v none * (v none * ((k + 2 : ℝ) * (k + 1 : ℝ) * w S)) +
      (∑ a : α, v none * (v (some a) * (if a ∈ S then 0 else (k + 1 : ℝ) * w (insert a S)))) +
      (∑ a : α, (v (some a) * (v none * (if a ∈ S then 0 else (k + 1 : ℝ) * w (insert a S))) +
        (∑ b : α, v (some a) * (v (some b) *
          (if a ∈ S ∨ b ∈ S ∨ a = b then 0 else w (insert a (insert b S))))))) = _
    have hcross (c : ℝ) (a : α) :
        c * (v (some a) * (if a ∈ S then 0 else (k + 1 : ℝ) * w (insert a S))) =
          if a ∈ S then 0 else (k + 1 : ℝ) * c * y a := by
      by_cases ha : a ∈ S
      · simp [ha]
      · simp only [if_neg ha]
        dsimp only [y]
        ring
    have hcross' (a : α) :
        v (some a) * (v none * (if a ∈ S then 0 else (k + 1 : ℝ) * w (insert a S))) =
          if a ∈ S then 0 else (k + 1 : ℝ) * v none * y a := by
      rw [mul_left_comm, hcross]
    have hlabel (a b : α) :
        v (some a) * (v (some b) *
          (if a ∈ S ∨ b ∈ S ∨ a = b then 0 else w (insert a (insert b S)))) =
          if a ∈ S then 0 else if b ∈ S then 0 else
            v (some a) * v (some b) * (if a = b then 0 else w (insert a (insert b S))) := by
      by_cases ha : a ∈ S <;> by_cases hb : b ∈ S <;>
        by_cases hab : a = b <;> simp [ha, hb, hab, mul_assoc]
    simp_rw [hcross, hcross', hlabel, Finset.sum_add_distrib,
      Finset.sum_ite_irrel, Finset.sum_const_zero, sumT]
    rw [← Finset.mul_sum]
    dsimp only [Y, B]
    ring
  rw [hquad]
  have hv' : (k + 2 : ℝ) * w S * v none + Y = 0 := hv
  have hY : Y = -((k + 2 : ℝ) * w S * v none) := by linarith
  rw [hY] at hbound ⊢
  have hm : (0 : ℝ) < (k + 2 : ℝ) := by positivity
  have hW := hw S
  have hid : (k + 2 : ℝ) * w S *
      ((k + 2 : ℝ) * (k + 1 : ℝ) * w S * v none ^ 2 +
        2 * (k + 1 : ℝ) * v none * -((k + 2 : ℝ) * w S * v none) + B) =
      (k + 2 : ℝ) * (w S * B) -
        ((k + 2 : ℝ) - 1) * (-((k + 2 : ℝ) * w S * v none)) ^ 2 := by ring
  apply (mul_le_mul_iff_right₀ (mul_pos hm hW)).mp
  rw [mul_zero, hid]
  exact sub_nonpos.mpr hbound

end CountingMatroid.Analysis.RankWeightResidualSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the residual signature using exact rank-weight closure-class coefficients and a sharp cardinality quadratic bound. Corrected the earlier informal sign calculation: the initial three terms on the hyperplane are positive Y²/(k+2), which the Cauchy–Schwarz correction cancels.
* 2026-10-09 · decomposed · chose the explicit weighted hyperplane, proved positivity of every rank weight, and expanded the matrix quadratic. The remaining sign calculation requires the parallel-class decomposition of rank increments after contracting the selected set.
-/
