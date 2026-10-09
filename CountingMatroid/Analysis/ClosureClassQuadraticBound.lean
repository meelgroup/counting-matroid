import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Tactic

set_option autoImplicit false

/-! The quadratic correction indexed by equal closure classes is nonnegative:
it is a sum of squares of the sums within each class. -/

namespace CountingMatroid.Analysis.ClosureClassQuadraticBound
open scoped BigOperators

/-- INTERNAL: An equality kernel is the sum of the squares of its fiber sums.
TEXLINE: main.tex:334-348 -/
theorem closure_class_kernel_eq_sum_sq {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (u : α → ℝ) :
    (∑ a ∈ T, ∑ b ∈ T, if f a = f b then u a * u b else 0) =
      ∑ j ∈ T.image f, (∑ a ∈ T with f a = j, u a) ^ 2 := by
  rw [← Finset.sum_fiberwise_of_maps_to
    (s := T) (t := T.image f) (g := f)
    (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩)
    (fun a => ∑ b ∈ T, if f a = f b then u a * u b else 0)]
  apply Finset.sum_congr rfl
  intro j hj
  have hinner (a : α) (ha : a ∈ T.filter (fun a => f a = j)) :
      (∑ b ∈ T, if f a = f b then u a * u b else 0) =
        u a * ∑ b ∈ T with f b = j, u b := by
    have ha' := (Finset.mem_filter.mp ha).2
    rw [Finset.sum_filter, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro b hb
    simp only [ha', eq_comm (a := j), mul_ite, mul_zero]
  rw [Finset.sum_congr rfl hinner, ← Finset.sum_mul]
  ring

/-- INTERNAL: An equality kernel is positive semidefinite on every finite set.
TEXLINE: main.tex:334-348 -/
theorem closure_class_kernel_nonneg {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (u : α → ℝ) :
    0 ≤ ∑ a ∈ T, ∑ b ∈ T, if f a = f b then u a * u b else 0 := by
  rw [closure_class_kernel_eq_sum_sq]
  exact Finset.sum_nonneg (fun j hj => sq_nonneg _)

/-- INTERNAL: Cauchy–Schwarz on the fiber sums bounds the equality kernel
using at most as many classes as there are labels.
TEXLINE: main.tex:334-348 -/
theorem closure_class_kernel_card_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (y : α → ℝ) :
    (∑ a ∈ T, y a) ^ 2 ≤ (T.card : ℝ) *
      (∑ a ∈ T, ∑ b ∈ T, if f a = f b then y a * y b else 0) := by
  have hk := closure_class_kernel_nonneg T f y
  rw [closure_class_kernel_eq_sum_sq] at hk ⊢
  have hf : (∑ j ∈ T.image f, ∑ a ∈ T with f a = j, y a) = ∑ a ∈ T, y a :=
    Finset.sum_fiberwise_of_maps_to (fun a ha => Finset.mem_image.mpr ⟨a, ha, rfl⟩) y
  rw [← hf]
  exact (sq_sum_le_card_mul_sum_sq (s := T.image f)
    (f := fun j => ∑ a ∈ T with f a = j, y a)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast Finset.card_image_le)
        hk)

/-- INTERNAL: The discounted pair form satisfies the sharp cardinality bound.
Combining Cauchy–Schwarz for labels and for classes supplies the homogenizer
hyperplane estimate.
TEXLINE: main.tex:334-348 -/
theorem parallel_class_card_quadratic_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1)
    (y : α → ℝ) :
    (T.card : ℝ) * (∑ a ∈ T, ∑ b ∈ T,
      (if a = b then 0 else if f a = f b then q else 1) * y a * y b)
        ≤ ((T.card : ℝ) - 1) * (∑ a ∈ T, y a) ^ 2 := by
  have hdiag := sq_sum_le_card_mul_sum_sq (s := T) (f := y)
  have hclass := closure_class_kernel_card_bound T f y
  have hid : (∑ a ∈ T, y a) ^ 2 -
      (∑ a ∈ T, ∑ b ∈ T,
        (if a = b then 0 else if f a = f b then q else 1) * y a * y b) =
      q * (∑ a ∈ T, y a ^ 2) +
        (1 - q) * (∑ a ∈ T, ∑ b ∈ T, if f a = f b then y a * y b else 0) := by
    rw [pow_two, Finset.sum_mul_sum, ← Finset.sum_sub_distrib,
      Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro a ha
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    have hsingle : (∑ b ∈ T, if a = b then q * (y a) ^ 2 else 0) = q * (y a) ^ 2 := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro b hb hba; simp [Ne.symm hba]
      · exact fun h => (h ha).elim
    rw [← hsingle, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro b hb
    by_cases hab : a = b
    · subst b; simp; ring
    · by_cases hf : f a = f b
      · simp only [if_neg hab, if_pos hf, zero_add]
        ring
      · simp [hab, hf]
  have hqdiag := mul_nonneg hq (sub_nonneg.mpr hdiag)
  have hqclass := mul_nonneg (sub_nonneg.mpr hqone) (sub_nonneg.mpr hclass)
  nlinarith [mul_nonneg (show (0 : ℝ) ≤ T.card by positivity) (sq_nonneg (∑ a ∈ T, y a))]

/-- INTERNAL: The sharp pair bound also allows loops, whose classes are
kept separate so that they receive no pair discount.
TEXLINE: main.tex:334-348 -/
theorem parallel_class_quadratic_bound {α β : Type} [DecidableEq α] [DecidableEq β]
    (T : Finset α) (f : α → β) (P : α → Prop) [DecidablePred P]
    (q : ℝ) (hq : 0 ≤ q) (hqone : q ≤ 1) (y : α → ℝ) :
    (T.card : ℝ) * (∑ a ∈ T, ∑ b ∈ T,
      (if a = b then 0 else if P a ∧ P b ∧ f a = f b then q else 1) * y a * y b)
        ≤ ((T.card : ℝ) - 1) * (∑ a ∈ T, y a) ^ 2 := by
  let g : α → α ⊕ β := fun a => if P a then Sum.inr (f a) else Sum.inl a
  have hcoeff (a b : α) :
      (if a = b then 0 else if g a = g b then q else 1) =
        (if a = b then 0 else if P a ∧ P b ∧ f a = f b then q else 1) := by
    by_cases hab : a = b
    · simp [hab]
    · by_cases ha : P a <;> by_cases hb : P b <;> simp [g, ha, hb, hab]
  simpa only [hcoeff] using parallel_class_card_quadratic_bound T g q hq hqone y

end CountingMatroid.Analysis.ClosureClassQuadraticBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · expressed the class kernel as a sum of fiber squares and combined label and class Cauchy–Schwarz bounds to prove the sharp cardinality estimate, including undiscounted loops.
-/

