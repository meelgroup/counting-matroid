import CountingMatroid.Analysis.ChainStepIntervalReplay
import Mathlib.Data.Fintype.Vector
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Finite uniform tape disintegration at a successful fixed endpoint cursor. -/
namespace CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: The defaulted finite tape associated with a bit list. -/
def finiteTape (bits : List Bool) : ℕ → Bool := fun i => (bits[i]?).getD false

/-- INTERNAL: Uniform mass of an event on the fresh suffix after a fixed head. -/
noncomputable def fairMass (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) : ℝ := by
  classical
  exact ∑ bits : List.Vector Bool t,
    if E (finiteTape (head ++ bits.val)) then 1 / (2 : ℝ) ^ t else 0

/-- INTERNAL: Split a finite uniform sum into its prefix and suffix sums. -/
theorem sum_split (t k : ℕ) (hk : k ≤ t) (f : List Bool → ℝ) :
    (∑ bits : List.Vector Bool t, f bits.val) =
      ∑ pref : List.Vector Bool k, ∑ tail : List.Vector Bool (t-k),
        f (pref.val ++ tail.val) := by
  classical
  let join : List.Vector Bool k × List.Vector Bool (t-k) → List.Vector Bool t :=
    fun p => ⟨p.1.val ++ p.2.val, by simp [Nat.add_sub_of_le hk]⟩
  have hj : Function.Bijective join := by
    constructor
    · intro a b heq
      have hv := congrArg Subtype.val heq
      have hp : a.1.val = b.1.val := by
        have h := congrArg (List.take k) hv
        simpa [join, List.take_append, a.1.2, b.1.2] using h
      have ht : a.2.val = b.2.val := by
        have h := congrArg (List.drop k) hv
        simpa [join, List.drop_append, a.1.2, b.1.2] using h
      exact Prod.ext (Subtype.ext hp) (Subtype.ext ht)
    · intro bits
      refine ⟨(⟨bits.val.take k, by simp [bits.2, Nat.min_eq_left hk]⟩,
        ⟨bits.val.drop k, by simp [bits.2]⟩), ?_⟩
      exact Subtype.ext (List.take_append_drop k bits.val)
  calc
    _ = ∑ p : List.Vector Bool k × List.Vector Bool (t-k), f (join p).val :=
      (Fintype.sum_bijective join hj _ _ (fun _ => rfl)).symm
    _ = _ := Fintype.sum_prod_type _

/-- INTERNAL: Uniform event mass factors across a deterministic suffix cut. -/
theorem fairMass_split (head : List Bool) (t k : ℕ) (hk : k ≤ t)
    (E : (ℕ → Bool) → Prop) :
    fairMass head t E = ∑ pref : List.Vector Bool k,
      (1 / (2 : ℝ) ^ k) * fairMass (head ++ pref.val) (t-k) E := by
  classical
  unfold fairMass
  rw [sum_split t k hk (fun bits => if E (finiteTape (head ++ bits)) then 1 / (2 : ℝ)^t else 0)]
  have hp : (1 / (2 : ℝ) ^ t) =
      (1 / (2 : ℝ) ^ k) * (1 / (2 : ℝ) ^ (t-k)) := by
    rw [one_div_mul_one_div, ← pow_add, Nat.add_sub_of_le hk]
  simp only [Finset.mul_sum, List.append_assoc]
  apply Finset.sum_congr rfl
  intro pref _
  apply Finset.sum_congr rfl
  intro tail _
  split_ifs <;> simp [hp]

/-- INTERNAL: Appending fresh bits leaves every bit in the old prefix fixed. -/
theorem finiteTape_append_agree (head tail₁ tail₂ : List Bool) (i : ℕ)
    (hi : i < head.length) :
    finiteTape (head ++ tail₁) i = finiteTape (head ++ tail₂) i := by
  unfold finiteTape
  rw [List.getElem?_append_left hi, List.getElem?_append_left hi]

/-- INTERNAL: Successful fixed-endpoint fibers are cylinders at their ending
cursor, so a uniform continuation bound multiplies the unnormalised fiber mass.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem stopped_fiber_bound {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option α) (cursor : α → ℕ)
    (hf : ChainStepIntervalReplay.SuccessReplay f cursor head.length)
    (a : α) (ha : head.length ≤ cursor a) (hc : cursor a ≤ head.length + t)
    (E : (ℕ → Bool) → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ pref : List.Vector Bool (cursor a - head.length),
      f (finiteTape (head ++ pref.val)) = some a →
      fairMass (head ++ pref.val) (t - (cursor a - head.length)) E ≤ B) :
    fairMass head t (fun tape => f tape = some a ∧ E tape) ≤
      fairMass head t (fun tape => f tape = some a) * B := by
  classical
  let k := cursor a - head.length
  have hk : k ≤ t := by dsimp [k]; omega
  have hlen (pref : List.Vector Bool k) : (head ++ pref.val).length = cursor a := by
    simp only [List.length_append, pref.2]
    dsimp [k]
    omega
  have hfiber (pref : List.Vector Bool k) (tail : List Bool) :
      f (finiteTape ((head ++ pref.val) ++ tail)) = some a ↔
        f (finiteTape (head ++ pref.val)) = some a := by
    have hagree : ∀ i, i < cursor a →
        finiteTape ((head ++ pref.val) ++ tail) i = finiteTape (head ++ pref.val) i := by
      intro i hi
      simpa only [List.append_nil] using
        finiteTape_append_agree (head ++ pref.val) tail [] i (by rw [hlen]; exact hi)
    constructor <;> intro h
    · exact (hf _ a h).2 _ (fun i _ hi => hagree i hi)
    · exact (hf _ a h).2 _ (fun i _ hi => (hagree i hi).symm)
  rw [fairMass_split head t k hk, fairMass_split head t k hk, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro pref _
  by_cases hinit : f (finiteTape (head ++ pref.val)) = some a
  · have hleft : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a ∧ E tape) = fairMass (head ++ pref.val) (t-k) E := by
      unfold fairMass
      apply Finset.sum_congr rfl
      intro tail _
      simp +instances only [hfiber pref tail.val, hinit, true_and]
    have hright : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a) = 1 := by
      unfold fairMass
      simp_rw [hfiber, hinit, if_true]
      simp [card_vector]
    rw [hleft, hright, mul_one]
    exact mul_le_mul_of_nonneg_left (hcont pref hinit) (by positivity)
  · have hz : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a) = 0 := by
      unfold fairMass
      simp_rw [hfiber, hinit, if_false]
      simp
    have hz' : fairMass (head ++ pref.val) (t-k)
        (fun tape => f tape = some a ∧ E tape) = 0 := by
      unfold fairMass
      simp_rw [hfiber, hinit, false_and, if_false]
      simp
    rw [hz, hz']
    simp

/-- INTERNAL: Event mass is nonnegative. -/
theorem fairMass_nonneg (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) :
    0 ≤ fairMass head t E := by
  classical
  exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)

/-- INTERNAL: Inclusion of finite-tape events increases their mass. -/
theorem fairMass_mono (head : List Bool) (t : ℕ) (E F : (ℕ → Bool) → Prop)
    (h : ∀ bits : List.Vector Bool t,
      E (finiteTape (head ++ bits.val)) → F (finiteTape (head ++ bits.val))) :
    fairMass head t E ≤ fairMass head t F := by
  classical
  apply Finset.sum_le_sum
  intro bits _
  by_cases he : E (finiteTape (head ++ bits.val))
  · simp only [he, h bits he, if_true, le_refl]
  · simp only [he, if_false]
    split_ifs <;> positivity

/-- INTERNAL: Sum disjoint stopping-cursor fibers, keeping their continuation events. -/
theorem fairMass_stop_sum {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option (α × ℕ)) (a : α) (E : (ℕ → Bool) → ℕ → Prop) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop) ∧ E tape stop) =
    ∑ stop : Fin (head.length + t + 1),
      fairMass head t (fun tape => f tape = some (a, stop.val) ∧ E tape stop.val) := by
  classical
  unfold fairMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bits _
  let tape := finiteTape (head ++ bits.val)
  dsimp only
  simp only [show finiteTape (head ++ bits.val) = tape from rfl]
  by_cases he : ∃ stop, stop ≤ head.length + t ∧ f tape = some (a, stop) ∧ E tape stop
  · obtain ⟨stop, hs, hf, hE⟩ := he
    let k : Fin (head.length + t + 1) := ⟨stop, by omega⟩
    rw [if_pos ⟨stop, hs, hf, hE⟩, Finset.sum_eq_single k]
    · simp only [k, hf, hE, and_self, if_true]
    · intro j _ hj
      apply if_neg
      rintro ⟨hjf, _⟩
      have hval := congrArg Prod.snd (Option.some.inj (hf.symm.trans hjf))
      apply hj
      exact Fin.ext hval.symm
    · simp
  · rw [if_neg he]
    symm
    apply Finset.sum_eq_zero
    intro j _
    apply if_neg
    intro hj
    exact he ⟨j.val, by omega, hj⟩

/-- INTERNAL: A stopped one-step event followed by uniformly bounded fresh
continuations has at most its covered marginal mass times that bound. -/
theorem stopped_next_bound {α : Type} (head : List Bool) (t : ℕ)
    (f : (ℕ → Bool) → Option (α × ℕ))
    (hf : ChainStepIntervalReplay.SuccessReplay f Prod.snd head.length)
    (a : α) (E : (ℕ → Bool) → ℕ → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ stop, head.length ≤ stop → stop ≤ head.length+t →
      ∀ pref : List.Vector Bool (stop-head.length),
      f (finiteTape (head ++ pref.val)) = some (a, stop) →
      fairMass (head ++ pref.val) (t-(stop-head.length)) (fun tape => E tape stop) ≤ B) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop) ∧ E tape stop) ≤
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      f tape = some (a, stop)) * B := by
  classical
  have hsplit := fairMass_stop_sum head t f a (fun _ _ => True)
  simp only [and_true] at hsplit
  rw [fairMass_stop_sum head t f a E, hsplit, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro stop _
  by_cases hstart : head.length ≤ stop.val
  · exact stopped_fiber_bound head t f Prod.snd hf (a, stop.val) hstart (by omega)
      (fun tape => E tape stop.val) B hB (hcont stop.val hstart (by omega))
  · have hnone : ∀ tape, f tape ≠ some (a, stop.val) := by
      intro tape hrun
      exact hstart (hf tape _ hrun).1
    have hz : fairMass head t (fun tape => f tape = some (a, stop.val)) = 0 := by
      unfold fairMass
      simp only [hnone, if_false, Finset.sum_const_zero]
    have hz' : fairMass head t (fun tape => f tape = some (a, stop.val) ∧ E tape stop.val) = 0 := by
      unfold fairMass
      simp only [hnone, false_and, if_false, Finset.sum_const_zero]
    rw [hz, hz']
    simp

end CountingMatroid.Analysis.FiniteStoppedFiberMass
