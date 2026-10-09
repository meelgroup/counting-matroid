import CountingMatroid.Analysis.SignatureOrthogonalNonpositive

set_option autoImplicit false

/-!
The block-matrix calculation for the transport Hessian. This module proves
the implication from a one-positive-direction bound to the balanced slot
inequality; it does not assert that operational weights satisfy that bound.
-/

namespace CountingMatroid.Analysis.SlotBlockSignature

open scoped BigOperators

/-- INTERNAL: The old-hole block and two new coordinates, with the opposite
child totals in the mixed blocks.
TEXLINE: main.tex:595-601 -/
def slotBlockMatrix {α : Type*} (V : α → α → ℝ) (sₐ sᵦ : α → ℝ)
    (u : ℝ) : Matrix (α ⊕ Bool) (α ⊕ Bool) ℝ
  | .inl i, .inl j => V i j
  | .inl i, .inr b => if b then sₐ i else sᵦ i
  | .inr b, .inl i => if b then sₐ i else sᵦ i
  | .inr b, .inr c => if b = c then 0 else u

/-- INTERNAL: Extend an old-hole vector by the two new coordinate values.
TEXLINE: main.tex:605-625 -/
def slotBlockVector {α : Type*} (h : α → ℝ) (x y : ℝ) : α ⊕ Bool → ℝ :=
  Sum.elim h (fun b => if b then y else x)

/-- INTERNAL: Expansion of the transport block matrix's quadratic form.
TEXLINE: main.tex:595-625 -/
theorem slot_block_eval {α : Type*} [Fintype α] [DecidableEq α]
    (V : α → α → ℝ) (sₐ sᵦ h : α → ℝ) (u x y : ℝ) :
    (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm' (slotBlockVector h x y) =
      (∑ i, ∑ j, V i j * h i * h j) +
        2 * x * (∑ i, sᵦ i * h i) +
        2 * y * (∑ i, sₐ i * h i) + 2 * u * x * y := by
  change Matrix.toLinearMap₂' ℝ (slotBlockMatrix V sₐ sᵦ u)
    (slotBlockVector h x y) (slotBlockVector h x y) = _
  rw [Matrix.toLinearMap₂'_apply]
  simp only [Fintype.sum_sum_type, Fintype.sum_bool, slotBlockMatrix,
    slotBlockVector, Sum.elim_inl, Sum.elim_inr, Bool.false_eq_true,
    Bool.true_eq_false, ite_true, ite_false, smul_eq_mul,
    mul_zero, zero_mul, Finset.sum_add_distrib]
  ring_nf
  have hsum (c : ℝ) (s : α → ℝ) :
      (∑ i, c * h i * s i) = c * ∑ i, s i * h i := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hdouble : (∑ i, ∑ j, h i * h j * V i j) =
      ∑ i, ∑ j, V i j * h i * h j := by
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hsum, hsum, hdouble]
  ring

/-- PAPER: main.tex:605-625
The one-positive-direction signature implies the balanced slot inequality,
using e=(0,1,1), on which the quadratic form equals 2u>0. -/
theorem slot_block_nonpositive {α : Type*} [Fintype α] [DecidableEq α]
    (V : α → α → ℝ) (sₐ sᵦ : α → ℝ) (u : ℝ) (hu : 0 < u)
    (hsig : sigPos (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm' ≤ 1)
    (h : α → ℝ) (x y : ℝ)
    (hbalance : (∑ i, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0) :
    (∑ i, ∑ j, V i j * h i * h j) +
      2 * x * (∑ i, sᵦ i * h i) +
      2 * y * (∑ i, sₐ i * h i) + 2 * u * x * y ≤ 0 := by
  let Q := (slotBlockMatrix V sₐ sᵦ u).toQuadraticForm'
  let e : α ⊕ Bool → ℝ := slotBlockVector (fun _ => 0) 1 1
  let v : α ⊕ Bool → ℝ := slotBlockVector h x y
  have he : 0 < Q e := by
    dsimp only [Q, e]
    rw [slot_block_eval]
    simpa using (mul_pos (by norm_num : (0 : ℝ) < 2) hu)
  have hev : e + v = slotBlockVector h (x + 1) (y + 1) := by
    ext j
    cases j with
    | inl i => simp [e, v, slotBlockVector]
    | inr b => cases b <;> simp [e, v, slotBlockVector, add_comm]
  have horth : Q.IsOrtho e v := by
    rw [QuadraticMap.isOrtho_def, hev]
    dsimp only [Q, e, v]
    simp only [slot_block_eval]
    simp only [mul_zero, Finset.sum_const_zero] 
    simp_rw [add_mul, Finset.sum_add_distrib] at hbalance
    nlinarith [hbalance]
  have hn := SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive
    Q hsig e v he (QuadraticMap.associated_isOrtho.mpr horth)
  simpa only [Q, v, slot_block_eval] using hn

end CountingMatroid.Analysis.SlotBlockSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · expanded the opposite-child block matrix and proved the balanced slot inequality from its one-positive-direction signature, using the positive vector (0,1,1).
-/
