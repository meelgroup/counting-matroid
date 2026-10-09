import CountingMatroid.Analysis.ConditionalTransversalSlots

set_option autoImplicit false

/-!
The operational classifier bridge at the terminal cliques of conditional
transversal transport. The ordinary-hole case is an ordered defect and the
branching-pair-hole case is an encoded transversal. A local classifier-fold
invariant proves its forward classification without a downstream import cycle.
-/

namespace CountingMatroid.Analysis.ConditionalLeafClassifier

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalTransversalSlots
open CountingMatroid.Analysis.LeafCliqueFlow
open CountingMatroid.Analysis.TransversalPartition

/-- INTERNAL: Classify the actual terminal vertex from the displayed-hole
shape of a conditional transversal demand tree.
TEXLINE: main.tex:670-674,810-826 -/
theorem conditional_leaf_classifier {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (choices : Fin n → Bool) (R : PairedSet n)
    (hR : R = {(k, false), (k, true)} ∪
      (ordinarySlots σ k).image (fun t => (t, choices t))) (hole : R) :
    (classifyState (leafVertex (fixedLabels σ) R hole)).val =
      if hole.val.1 = k then .transversal else .defect hole.val.1 k := by
  classical
  have hrespect := conditional_leaf_respects σ k hk choices R hR hole
  by_cases hbranch : hole.val.1 = k
  · rw [if_pos hbranch]
    have hholeeq : hole.val = (k, hole.val.2) := Prod.ext hbranch rfl
    have hnot : hole.val ∉ (ordinarySlots σ k).image (fun t => (t, choices t)) := by
      rintro hm
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hm
      have htk : t = k := (congrArg Prod.fst he).trans hbranch
      exact ((mem_ordinary_slots σ k t).mp ht).2 htk
    have hcompletion : DefectSlotSplitSignature.SlotCompletion (fixedLabels σ)
        {(k, false), (k, true)} (ordinarySlots σ k) (k, hole.val.2)
          (leafVertex (fixedLabels σ) R hole) := by
      refine ⟨choices, ?_⟩
      simp only [leafVertex, hR, Finset.erase_union_distrib, Finset.erase_eq_of_notMem hnot]
      rw [hholeeq, Finset.union_assoc]
    obtain ⟨A, _, hencode⟩ := (root_completion_iff σ k hk (!hole.val.2) _).mp
      (by simpa only [Bool.not_not] using hcompletion)
    rw [hencode]
    let step := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) => do
      let x ← CountingMatroid.Model.Operations.containsPaired (transversalState A) (i, false)
      let y ← CountingMatroid.Model.Operations.containsPaired (transversalState A) (i, true)
      if x then
        if y then
          let seen ← CountingMatroid.Model.Operations.isSome acc.2.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (acc.1, some i, acc.2.2)
        else pure acc
      else
        if y then pure acc
        else
          let seen ← CountingMatroid.Model.Operations.isSome acc.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (some i, acc.2.1, acc.2.2)
    have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
        (step acc i).val = acc := by
      by_cases hi : i ∈ A <;>
        simp [step, CountingMatroid.Model.Operations.containsPaired, transversalState, hi]
    have hfold (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
        (Arlib.Computation.Charged.foldl step l acc).val = acc := by
      induction l generalizing acc with
      | nil => rfl
      | cons i l ih => rw [Arlib.Computation.Charged.val_foldl_cons, hstep, ih]
    unfold CountingMatroid.Program.classifyState
    change ((do
      let result ← Arlib.Computation.Charged.foldl step (List.finRange n) (none, none, false)
      if result.2.2 then pure .invalid else
        match result.1, result.2.1 with
        | none, none => pure .transversal
        | some i, some j => do
            let diagonal ← CountingMatroid.Model.Operations.indexEqual i j
            if diagonal then pure .invalid else pure (.defect i j)
        | _, _ => pure .invalid) :
          Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
            CountingMatroid.Model.Operations.Cell (StateKind n)).val = _
    simp [hfold]
  · rw [if_neg hbranch]
    apply (InitialMultipliersGood.classify_defect_iff _ ⟨hole.val.1, k, hbranch⟩).mpr
    -- Concrete route: hR and hole.property identify the removed label as
    -- (hole.1, choices hole.1), with hole.1 an ordinary slot. Thus exactly
    -- that pair is empty and exactly k is full; all other pairs are single.
    have hhole : hole.val ∈ {(k, false), (k, true)} ∪
        (ordinarySlots σ k).image (fun t => (t, choices t)) := by
      rw [← hR]
      exact hole.property
    have hchosen : hole.val = (hole.val.1, choices hole.val.1) ∧
        hole.val.1 ∈ ordinarySlots σ k := by
      rcases Finset.mem_union.mp hhole with hm | hm
      · rcases Finset.mem_insert.mp hm with he | he
        · exact False.elim (hbranch (congrArg Prod.fst he))
        · exact False.elim (hbranch (congrArg Prod.fst (Finset.mem_singleton.mp he)))
      · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hm
        have hfirst : t = hole.val.1 := congrArg Prod.fst he
        subst t
        exact ⟨he.symm, ht⟩
    obtain ⟨hhσ, hhne⟩ := (mem_ordinary_slots σ k hole.val.1).mp hchosen.2
    have hmem (i : Fin n) (b : Bool) :
        (i, b) ∈ leafVertex (fixedLabels σ) R hole ↔
        σ i = some b ∨
          ((i, b) ≠ hole.val ∧ (i = k ∨
            (σ i = none ∧ i ≠ k ∧ choices i = b))) := by
      simp only [leafVertex, Finset.mem_union, mem_fixed_labels, Finset.mem_erase, hR]
      have him : (i, b) ∈ (ordinarySlots σ k).image (fun t => (t, choices t)) ↔
          σ i = none ∧ i ≠ k ∧ choices i = b := by
        simp [mem_ordinary_slots, and_assoc]
      rw [him]
      cases b <;> simp
    constructor <;> intro i
    all_goals
      simp only [DefectIndex.emptyPair, DefectIndex.fullPair]
      rw [hmem, hmem, hchosen.1]
      by_cases hik : i = k
      · subst i
        simp [hk, hbranch, Ne.symm hbranch]
      · by_cases hih : i = hole.val.1
        · subst i
          cases choices hole.val.1 <;> simp [hhσ, hbranch]
        · cases hσ : σ i with
          | none => cases choices i <;> simp [hσ, hik, hih]
          | some c => cases c <;> simp [hσ, hik, hih]

end CountingMatroid.Analysis.ConditionalLeafClassifier

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed branching-hole transversal classification with a local charged-fold invariant; both terminal-hole cases are now proved.

* 2026-10-09 · partial · proved ordinary-hole defect classification from the exact occupancy predicate and the public defect characterization. The branching-hole case is encoded using root_completion_iff and ends at the existing downstream transversal_state_classified statement; a mechanical upstream move is needed to import that proof here.
-/
