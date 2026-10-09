import CountingMatroid.Analysis.FiniteStoppedFiberMass

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! A finite stopped operation can be followed by a uniformly bounded fresh
continuation without conditioning away its abort mass. -/
namespace CountingMatroid.Analysis.FiniteStoppedKernelBind
open CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Disintegrate an adaptive initializer by its complete successful
result and consumed prefix, then apply a fresh-suffix continuation bound.
Only initializer results occurring in the continued event need be covered.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem stopped_kernel_bind_bound {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option α) (cursor : α → ℕ)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (E : (ℕ → Bool) → α → Prop) (B : α → ℝ) (hB : ∀ a, 0 ≤ B a)
    (hcovered : ∀ bits : List.Vector Bool t, ∀ a,
      f (finiteTape (head ++ bits.val)) = some a →
      E (finiteTape (head ++ bits.val)) a → cursor a ≤ head.length + t)
    (hcont : ∀ a, head.length ≤ cursor a → cursor a ≤ head.length + t →
      ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length))
        (fun tape => E tape a) ≤ B a) :
    fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) ≤
      ∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((f (finiteTape (head ++ bits.val))).map B).getD 0 := by
  classical
  let R := fun bits : List.Vector Bool t => f (finiteTape (head ++ bits.val))
  let S := Finset.univ.image R
  let C := fun tape outcome => match outcome with
    | none => False
    | some a => E tape a
  have hleft : fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) =
      ∑ outcome ∈ S, fairMass head t (fun tape => f tape = outcome ∧ C tape outcome) := by
    unfold fairMass
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bits _
    have hm : R bits ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ bits)
    have he : (∃ a, f (finiteTape (head ++ bits.val)) = some a ∧
        E (finiteTape (head ++ bits.val)) a) ↔ C (finiteTape (head ++ bits.val)) (R bits) := by
      cases hr : R bits with
      | none => simp +instances [R] at hr; simp [hr, C]
      | some a => simp +instances [R] at hr; simp [hr, C]
    dsimp only
    simp +instances only [he]
    rw [Finset.sum_eq_single (R bits)]
    · simp +instances only [show f (finiteTape (head ++ bits.val)) = R bits from rfl,
        true_and]
    · intro other _ hne
      exact if_neg (fun h => hne h.1.symm)
    · exact fun h => False.elim (h hm)
  have hright : (∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
      ((f (finiteTape (head ++ bits.val))).map B).getD 0) =
      ∑ outcome ∈ S, fairMass head t (fun tape => f tape = outcome) *
        (outcome.map B).getD 0 := by
    unfold fairMass
    simp only [Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bits _
    have hm : R bits ∈ S := Finset.mem_image_of_mem _ (Finset.mem_univ bits)
    change (1 / (2 : ℝ) ^ t) * ((R bits).map B).getD 0 = _
    simp only [ite_mul, zero_mul]
    change _ = ∑ outcome ∈ S,
      if R bits = outcome then (1 / (2 : ℝ) ^ t) * (outcome.map B).getD 0 else 0
    simp only [Finset.sum_ite_eq, hm, if_true]
  rw [hleft, hright]
  apply Finset.sum_le_sum
  intro outcome _
  cases outcome with
  | none =>
    simp only [C, and_false, fairMass, if_false, Finset.sum_const_zero,
      Option.map_none, Option.getD_none, mul_zero, le_refl]
  | some a =>
    simp only [C, Option.map_some, Option.getD_some]
    by_cases hocc : ∃ bits : List.Vector Bool t,
      f (finiteTape (head ++ bits.val)) = some a ∧ E (finiteTape (head ++ bits.val)) a
    · obtain ⟨bits, hfa, hEa⟩ := hocc
      exact stopped_fiber_bound head t f cursor hf a (hf _ a hfa).1
        (hcovered bits a hfa hEa) (fun tape => E tape a) (B a) (hB a)
        (hcont a (hf _ a hfa).1 (hcovered bits a hfa hEa))
    · have hz : fairMass head t (fun tape => f tape = some a ∧ E tape a) = 0 := by
        unfold fairMass
        apply Finset.sum_eq_zero
        intro bits _
        exact if_neg (fun h => hocc ⟨bits, h⟩)
      rw [hz]
      exact mul_nonneg (fairMass_nonneg _ _ _) (hB a)

/-- INTERNAL: The stopped-bind comparison with a finite state marginal and
an explicit coverage restriction on the initializer's ending cursor.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem stopped_kernel_bind_covered_bound {α Ω : Type} [Fintype Ω]
    (head : List Bool) (t : ℕ) (f : (ℕ → Bool) → Option α)
    (cursor : α → ℕ) (state : α → Ω)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (E : (ℕ → Bool) → α → Prop) (B : Ω → ℝ) (hB : ∀ x, 0 ≤ B x)
    (hcovered : ∀ bits : List.Vector Bool t, ∀ a,
      f (finiteTape (head ++ bits.val)) = some a →
      E (finiteTape (head ++ bits.val)) a → cursor a ≤ head.length + t)
    (hcont : ∀ a, head.length ≤ cursor a → cursor a ≤ head.length + t →
      ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length))
        (fun tape => E tape a) ≤ B (state a)) :
    fairMass head t (fun tape => ∃ a, f tape = some a ∧ E tape a) ≤
      ∑ x : Ω, fairMass head t (fun tape => ∃ a, f tape = some a ∧
        cursor a ≤ head.length + t ∧ state a = x) * B x := by
  classical
  let C := fun a => if cursor a ≤ head.length + t then B (state a) else 0
  have hbound := stopped_kernel_bind_bound head t f cursor hf E C
    (fun a => by dsimp only [C]; split_ifs <;> [exact hB _; exact le_rfl])
    hcovered (by
      intro a ha hc pref hf
      simpa only [C, hc, if_true] using hcont a ha hc pref hf)
  apply hbound.trans_eq
  unfold fairMass
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bits _
  have hterm (R : Option α) : (1 / (2 : ℝ)^t) * (R.map C).getD 0 =
      ∑ x : Ω, (if ∃ a, R = some a ∧ cursor a ≤ head.length+t ∧ state a = x
        then 1 / (2 : ℝ)^t else 0) * B x := by
    cases R with
    | none => simp only [Option.map_none, Option.getD_none, mul_zero,
        reduceCtorEq, false_and, exists_false, if_false, zero_mul, Finset.sum_const_zero]
    | some a =>
      simp only [Option.map_some, Option.getD_some, Option.some.injEq, exists_eq_left']
      by_cases hc : cursor a ≤ head.length + t
      · simp +instances only [exists_eq_left', hc, true_and, C, if_true, ite_mul, zero_mul,
          Finset.sum_ite_eq, Finset.mem_univ, if_true]
      · simp +instances only [exists_eq_left', hc, false_and, C, if_false, mul_zero,
          zero_mul, Finset.sum_const_zero]
  convert hterm (f (finiteTape (head ++ bits.val))) using 1
  apply Finset.sum_congr rfl
  intro x _
  split_ifs <;> rfl

end CountingMatroid.Analysis.FiniteStoppedKernelBind

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · complete-result finite stopped-bind disintegration and its covered state-marginal form; no finite type or bounded attempt-counter premise is imposed on initializer results.
-/
