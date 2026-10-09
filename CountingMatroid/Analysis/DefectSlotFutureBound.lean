import CountingMatroid.Analysis.SlotTransportFlow

set_option autoImplicit false
set_option maxRecDepth 2000
set_option maxHeartbeats 1000000

/-!
The off-subgraph root future totals count a subset of the full defect
fiber with the ordinary pair doubled. Thus the paper's transport estimate
can use the existing full defect partition sums as upper bounds.
-/

namespace CountingMatroid.Analysis.DefectSlotFutureBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature

/-- PAPER: main.tex:895-898
A root future entry counts a subset of the defect fiber with pair i
empty and pair t doubled, keeping one prescribed label at pair k. -/
theorem root_future_le_defect_partition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q)
    (i t k : Fin n) (hit : i ≠ t) (htk : t ≠ k) (hik : i ≠ k) (a b : Bool) :
    futureMatrix r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) t (i, !a) (k, b) ≤
        (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, t, hit⟩ : ℝ) := by
  classical
  have hpd : (i, !a) ≠ (k, b) := fun he => hik (congrArg Prod.fst he)
  have he : ((({(i, !a), (k, b)} : PairedSet n).erase (i, !a)).erase (k, b)) = ∅ := by
    rw [Finset.erase_insert (by simpa using hpd), Finset.erase_singleton]
  unfold futureMatrix FirstPhaseFailure.defectPartition
  rw [if_neg hpd, he]
  simp only [Finset.union_empty, Rat.cast_sum, apply_ite, Rat.cast_zero]
  apply Finset.sum_le_sum
  intro state _
  by_cases hs : ∃ choices : Fin n → Bool,
      state = {(k, !b)} ∪ {(t, false), (t, true)} ∪
        (((Finset.univ.erase i).erase k).erase t).image (fun s => (s, choices s))
  · obtain ⟨choices, heq⟩ := hs
    have him (j : Fin n) (c : Bool) :
        (j, c) ∈ (((Finset.univ.erase i).erase k).erase t).image (fun s => (s, choices s)) ↔
          j ∈ (((Finset.univ.erase i).erase k).erase t) ∧ c = choices j := by
      constructor
      · intro hh
        obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hh
        have hsj : s = j := congrArg Prod.fst he
        subst s
        exact ⟨hs, (congrArg Prod.snd he).symm⟩
      · rintro ⟨hj, hc⟩
        exact Finset.mem_image.mpr ⟨j, hj, Prod.ext rfl hc.symm⟩
    have hm (j : Fin n) (c : Bool) : (j, c) ∈ state ↔
        (j = k ∧ c = !b) ∨ j = t ∨
          (j ≠ i ∧ j ≠ k ∧ j ≠ t ∧ c = choices j) := by
      rw [heq]
      cases c <;>
        simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton,
          him, Finset.mem_erase, Finset.mem_univ, Prod.mk.injEq,
          exists_eq_left, and_true, true_and, Bool.false_eq_true, Bool.true_eq_false,
          false_and, and_false, or_false, false_or] <;> tauto
    have hclass : (classifyState state).val = .defect i t := by
      apply (InitialMultipliersGood.classify_defect_iff state ⟨i, t, hit⟩).mpr
      constructor <;> intro j
      all_goals
        rw [hm j false, hm j true]
        by_cases hjI : j = i <;> by_cases hjT : j = t <;> by_cases hjK : j = k <;>
          cases b <;> cases hc : choices j <;>
          simp only [hjI, hjT, hjK, hc, Bool.not_false, Bool.not_true,
            Bool.false_eq_true, Bool.true_eq_false,
            true_and, and_true, false_and, and_false, or_true, true_or, or_false,
            false_or, not_true_eq_false, not_false_eq_true] <;> aesop
    rw [if_pos ⟨choices, heq⟩, if_pos hclass]
  · rw [if_neg hs]
    split_ifs
    · exact_mod_cast (pow_pos hq _).le
    · exact le_rfl

end CountingMatroid.Analysis.DefectSlotFutureBound
