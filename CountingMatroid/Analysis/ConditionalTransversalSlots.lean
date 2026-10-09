import CountingMatroid.Analysis.SlotLeafGeometry
import CountingMatroid.Analysis.ExchangeProposalGeometry
import CountingMatroid.Analysis.ConditionalDefectCoefficients
import CountingMatroid.Analysis.LeafCliqueFlow

set_option autoImplicit false

/-!
The fixed labels and ordinary slots for a conditional transversal split.
The completion predicates below connect the paper's slot recursion to the
existing assignment-indexed transversal sums.
-/

namespace CountingMatroid.Analysis.ConditionalTransversalSlots

open Classical
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion

/-- INTERNAL: Selected labels at the already assigned pairs.
TEXLINE: main.tex:810-817 -/
def fixedLabels {n : ℕ} (σ : Assignment n) : PairedSet n := by
  classical
  exact (Finset.univ.filter (fun i => σ i ≠ none)).image
    (fun i => (i, (σ i).getD false))

/-- INTERNAL: The ordinary slots are the unassigned pairs other than the
branching pair.
TEXLINE: main.tex:810-817 -/
def ordinarySlots {n : ℕ} (σ : Assignment n) (k : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => σ i = none ∧ i ≠ k)

/-- INTERNAL: Membership in the fixed labels records precisely a prescribed bit.
TEXLINE: main.tex:810-817 -/
theorem mem_fixed_labels {n : ℕ} (σ : Assignment n) (i : Fin n) (b : Bool) :
    (i, b) ∈ fixedLabels σ ↔ σ i = some b := by
  classical
  cases h : σ i <;> simp [fixedLabels, h]

/-- INTERNAL: Membership in the ordinary slot list is the summation guard
in the assigned theorem.
TEXLINE: main.tex:810-817 -/
theorem mem_ordinary_slots {n : ℕ} (σ : Assignment n) (k i : Fin n) :
    i ∈ ordinarySlots σ k ↔ σ i = none ∧ i ≠ k := by
  classical
  simp [ordinarySlots]

/-- INTERNAL: A completed binary demand tree displays one selected label
from each processed pair in addition to the original holes.
TEXLINE: main.tex:516-520,670-674 -/
theorem leaf_holes_shape {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (hnodup : slots.Nodup)
    (node : DemandNode n)
    (leaf : DemandNode n) (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots node) :
    ∃ choices : Fin n → Bool,
      leaf.holes = node.holes ∪ slots.toFinset.image (fun t => (t, choices t)) := by
  classical
  induction slots generalizing node with
  | nil =>
    have heq : leaf = node := by simpa [leafNodes] using hleaf
    subst leaf
    exact ⟨fun _ => false, by simp⟩
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    have child (c : Bool) (hl : leaf ∈ leafNodes r o₁ o₂ q B slots
        (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c)) :
        ∃ choices : Fin n → Bool,
          leaf.holes = node.holes ∪ (t :: slots).toFinset.image
            (fun s => (s, choices s)) := by
      obtain ⟨choices, hc⟩ := ih hnd _ hl
      refine ⟨Function.update choices t c, ?_⟩
      have himage : slots.toFinset.image (fun s => (s, Function.update choices t c s)) =
          slots.toFinset.image (fun s => (s, choices s)) := by
        apply Finset.image_congr
        intro s hs
        have hst : s ≠ t := by rintro rfl; exact ht (List.mem_toFinset.mp hs)
        simp only [Function.update_of_ne hst]
      rw [List.toFinset_cons, Finset.image_insert, Function.update_self, himage]
      simpa only [splitNode, Finset.insert_union, Finset.union_insert] using hc
    rcases List.mem_append.mp hleaf with ha | hb
    · exact child false ha
    · exact child true hb

/-- INTERNAL: Erasing the unchosen singleton leaves the selected bit at
one root hole.
TEXLINE: main.tex:810-817 -/
private theorem root_erase {n : ℕ} (k : Fin n) (b : Bool) :
    ({(k, false), (k, true)} : PairedSet n).erase (k, !b) = {(k, b)} := by
  ext ⟨i, d⟩
  cases b <;> cases d <;> simp

/-- INTERNAL: Explicit occupancy of a conditional transversal completion.
TEXLINE: main.tex:810-817 -/
private theorem completion_mem {n : ℕ} (σ : Assignment n) (k : Fin n)
    (b : Bool) (choices : Fin n → Bool) (i : Fin n) (d : Bool) :
    (i, d) ∈ fixedLabels σ ∪ {(k, b)} ∪
      (ordinarySlots σ k).image (fun t => (t, choices t)) ↔
    σ i = some d ∨ (i = k ∧ d = b) ∨
      (σ i = none ∧ i ≠ k ∧ choices i = d) := by
  classical
  simp [mem_fixed_labels, mem_ordinary_slots, eq_comm, and_assoc, or_left_comm]

/-- INTERNAL: Root slot completions are exactly encoded transversals
respecting the selected child assignment.
TEXLINE: main.tex:810-817 -/
theorem root_completion_iff {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (b : Bool) (state : PairedSet n) :
    SlotCompletion (fixedLabels σ) {(k, false), (k, true)}
      (ordinarySlots σ k) (k, !b) state ↔
    ∃ A : Finset (Fin n),
      SubsetRespects (Function.update σ k (some b)) A ∧ state = transversalState A := by
  classical
  constructor
  · rintro ⟨choices, hs⟩
    rw [root_erase] at hs
    have hm (i : Fin n) (d : Bool) : (i, d) ∈ state ↔
        σ i = some d ∨ (i = k ∧ d = b) ∨
          (σ i = none ∧ i ≠ k ∧ choices i = d) := by
      rw [hs]
      exact completion_mem σ k b choices i d
    have hpair (i : Fin n) : (i, false) ∈ state ↔ (i, true) ∉ state := by
      rw [hm, hm]
      by_cases hi : i = k
      · subst i; cases b <;> simp [hk]
      · cases hσ : σ i with
        | none => cases choices i <;> simp [hσ, hi]
        | some a => cases a <;> simp [hσ, hi]
    let A := Finset.univ.filter (fun i => (i, false) ∈ state)
    have heq : state = transversalState A := by
      ext ⟨i, d⟩
      cases d
      · simp [transversalState, A]
      · have hp := not_congr (hpair i)
        simpa [transversalState, A] using hp.symm
    refine ⟨A, ?_, heq⟩
    rw [subset_respects_iff, ← heq]
    intro i d hd
    by_cases hi : i = k
    · subst i
      have hdb : b = d := by simpa using hd
      subst d
      cases b <;> simp [hm, hk]
    · have hid : σ i = some d := by simpa [Function.update_of_ne hi] using hd
      cases d <;> simp [hm, hid, hi]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun i => decide (i ∉ A), ?_⟩
    rw [root_erase]
    ext ⟨i, d⟩
    rw [completion_mem]
    have hparent := (subset_respects_update σ k hk b A).mp hA
    have hbit : (i, d) ∈ transversalState A ↔ decide (i ∉ A) = d := by
      simp [transversalState]
    rw [hbit]
    by_cases hi : i = k
    · subst i
      simp [hk, hparent.2, eq_comm]
    · cases hσ : σ i with
      | none => simp [hσ, hi]
      | some a =>
        have ha := hparent.1 i a hσ
        simp [hσ, hi, ha, eq_comm]

/-- INTERNAL: Reindex a root completion moment by the existing subset
encoding, without introducing a new transversal distribution.
TEXLINE: main.tex:810-817 -/
theorem root_completion_sum {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (b : Bool) (f : PairedSet n → ℝ) :
    (∑ state : PairedSet n,
      if SlotCompletion (fixedLabels σ) {(k, false), (k, true)}
        (ordinarySlots σ k) (k, !b) state then f state else 0) =
    ∑ A : Finset (Fin n),
      if SubsetRespects (Function.update σ k (some b)) A then
        f (transversalState A) else 0 := by
  classical
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun A _ => transversalState A)
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact (root_completion_iff σ k hk b _).mpr ⟨A, hA, rfl⟩
  · intro A _ D _ hAD
    ext i
    have he := congrArg (fun state : PairedSet n => (i, false) ∈ state) hAD
    simpa [transversalState] using he
  · intro state hs
    obtain ⟨A, hA, hstate⟩ := (root_completion_iff σ k hk b state).mp
      (Finset.mem_filter.mp hs).2
    exact ⟨A, by simpa using hA, hstate.symm⟩
  · intro A _
    rfl

/-- INTERNAL: The root hole total is the corresponding conditional
transversal total, in the real scalar field used by transport.
TEXLINE: main.tex:810-817 -/
theorem root_transversal_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (k : Fin n) (hk : σ k = none) (b : Bool) :
    slotTotal r o₁ o₂ q (fixedLabels σ) {(k, false), (k, true)}
      (ordinarySlots σ k) (k, !b) =
      (transversalTotal r o₁ o₂ q (Function.update σ k (some b)) : ℝ) := by
  classical
  rw [slotTotal, root_completion_sum σ k hk b]
  unfold transversalTotal
  push_cast
  apply Finset.sum_congr rfl
  intro A _
  split_ifs <;> simp [transversalDeficiency]

/-- INTERNAL: The root configuration satisfies the admissibility
hypotheses retained by the demand recursion.
TEXLINE: main.tex:463-465,810-817 -/
theorem root_admissible {n : ℕ} (σ : Assignment n) (k : Fin n) (hk : σ k = none) :
    Disjoint (fixedLabels σ) ({(k, false), (k, true)} : PairedSet n) ∧
    (∀ t ∈ ordinarySlots σ k, ∀ b : Bool,
      (t, b) ∉ fixedLabels σ ∧ (t, b) ∉ ({(k, false), (k, true)} : PairedSet n)) ∧
    (fixedLabels σ).card + ({(k, false), (k, true)} : PairedSet n).card +
      (ordinarySlots σ k).card = n + 1 := by
  classical
  have hBR : Disjoint (fixedLabels σ) ({(k, false), (k, true)} : PairedSet n) := by
    rw [Finset.disjoint_right]
    intro e he
    rcases Finset.mem_insert.mp he with rfl | he
    · simp [mem_fixed_labels, hk]
    · have heq := Finset.mem_singleton.mp he
      subst e
      simp [mem_fixed_labels, hk]
  refine ⟨hBR, ?_, ?_⟩
  · intro t ht b
    obtain ⟨hσ, htk⟩ := (mem_ordinary_slots σ k t).mp ht
    simp [mem_fixed_labels, hσ, htk]
  · let assigned := Finset.univ.filter (fun i => σ i ≠ none)
    let free := Finset.univ.filter (fun i => σ i = none)
    have hbase : (fixedLabels σ).card = assigned.card := by
      apply Finset.card_image_of_injective
      intro i j hij
      exact congrArg Prod.fst hij
    have hslots : ordinarySlots σ k = free.erase k := by
      ext i
      simp [mem_ordinary_slots, free, and_comm]
    have hfree : k ∈ free := by simp [free, hk]
    have htotal : assigned.card + free.card = n := by
      have he := Finset.card_filter_add_card_filter_not (s := Finset.univ)
        (p := fun i : Fin n => σ i ≠ none)
      simpa [assigned, free] using he
    have hroot : ({(k, false), (k, true)} : PairedSet n).card = 2 := by simp
    rw [hbase, hroot, hslots, Finset.card_erase_of_mem hfree]
    have hpos := Finset.card_pos.mpr ⟨k, hfree⟩
    omega

/-- INTERNAL: The off-graph doubled-slot completions are exactly the
conditional ordered-defect class supplying the correction coefficient.
TEXLINE: main.tex:580-582,818-821 -/
theorem doubled_completion_iff {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (t : Fin n) (ht : t ∈ ordinarySlots σ k)
    (state : PairedSet n) :
    (∃ choices : Fin n → Bool,
      state = fixedLabels σ ∪ {(t, false), (t, true)} ∪
        ((ordinarySlots σ k).erase t).image (fun s => (s, choices s))) ↔
    Respects σ state ∧ (classifyState state).val = .defect k t := by
  classical
  obtain ⟨hσt, htk⟩ := (mem_ordinary_slots σ k t).mp ht
  constructor
  · rintro ⟨choices, rfl⟩
    let S := fixedLabels σ ∪ {(t, false), (t, true)} ∪
      ((ordinarySlots σ k).erase t).image (fun s => (s, choices s))
    have hm (i : Fin n) (d : Bool) : (i, d) ∈ S ↔
        σ i = some d ∨ i = t ∨
          (σ i = none ∧ i ≠ k ∧ i ≠ t ∧ choices i = d) := by
      have him : (i, d) ∈ ((ordinarySlots σ k).erase t).image
          (fun s => (s, choices s)) ↔
          i ≠ t ∧ (σ i = none ∧ i ≠ k) ∧ choices i = d := by
        simp [mem_ordinary_slots, and_assoc]
      simp only [S, Finset.mem_union, mem_fixed_labels, him]
      cases d <;> simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
        Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, false_or, or_false]
      all_goals tauto
    change Respects σ S ∧ (classifyState S).val = .defect k t
    refine ⟨?_, (InitialMultipliersGood.classify_defect_iff S ⟨k, t, htk.symm⟩).mpr ?_⟩
    · intro i d hid
      have hik : i ≠ k := by rintro rfl; rw [hk] at hid; cases hid
      have hit : i ≠ t := by rintro rfl; rw [hσt] at hid; cases hid
      cases d <;> simp [hm, hid, hik, hit]
    · constructor <;> intro i
      all_goals
        rw [hm, hm]
        by_cases hik : i = k
        · subst i; simp [hk, htk.symm]
        · by_cases hit : i = t
          · subst i; simp [hσt, htk]
          · cases hσi : σ i with
            | none => cases choices i <;> simp [hik, hit, hσi]
            | some c => cases c <;> simp [hik, hit, hσi]
  · rintro ⟨hrespect, hclass⟩
    obtain ⟨hempty, hfull⟩ :=
      (InitialMultipliersGood.classify_defect_iff state ⟨k, t, htk.symm⟩).mp hclass
    refine ⟨fun i => decide ((i, false) ∉ state), ?_⟩
    ext ⟨i, d⟩
    have hmem : (i, d) ∈ fixedLabels σ ∪ {(t, false), (t, true)} ∪
        ((ordinarySlots σ k).erase t).image
          (fun s => (s, decide ((s, false) ∉ state))) ↔
        σ i = some d ∨ i = t ∨
          (σ i = none ∧ i ≠ k ∧ i ≠ t ∧ decide ((i, false) ∉ state) = d) := by
      have him : (i, d) ∈ ((ordinarySlots σ k).erase t).image
          (fun s => (s, decide ((s, false) ∉ state))) ↔
          i ≠ t ∧ (σ i = none ∧ i ≠ k) ∧ decide ((i, false) ∉ state) = d := by
        simp [mem_ordinary_slots, and_assoc]
      simp only [Finset.mem_union, mem_fixed_labels, him]
      cases d <;> simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq,
        Bool.false_eq_true, Bool.true_eq_false, and_false, and_true, false_or, or_false]
      all_goals tauto
    rw [hmem]
    by_cases hik : i = k
    · subst i
      obtain ⟨hx, hy⟩ := (hempty k).mpr rfl
      cases d <;> simp [hx, hy, hk, htk.symm]
    · by_cases hit : i = t
      · subst i
        obtain ⟨hx, hy⟩ := (hfull t).mpr rfl
        cases d <;> simp [hx, hy]
      · have he := hempty i
        have hf := hfull i
        have hpair : (i, false) ∈ state ↔ (i, true) ∉ state := by
          simp only [hik, hit, iff_false] at he hf
          tauto
        cases hσi : σ i with
        | none =>
          cases d <;> by_cases hx : (i, false) ∈ state <;>
            simp_all
        | some c =>
          have hc := hrespect i c hσi
          cases c <;> cases d <;> simp_all

/-- INTERNAL: The root future-matrix entry is the ordered-defect
correction coefficient in the conditional node inequality.
TEXLINE: main.tex:580-582,818-821 -/
theorem root_future_defect_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (k : Fin n) (hk : σ k = none)
    (t : Fin n) (ht : t ∈ ordinarySlots σ k) :
    futureMatrix r o₁ o₂ q (fixedLabels σ) {(k, false), (k, true)}
      (ordinarySlots σ k) t (k, false) (k, true) =
      (defectTotal r o₁ o₂ q σ ⟨k, t, ((mem_ordinary_slots σ k t).mp ht).2.symm⟩ : ℝ) := by
  classical
  have he : (({(k, false), (k, true)} : PairedSet n).erase (k, false)).erase
      (k, true) = ∅ := by simp
  simp only [futureMatrix, Prod.mk.injEq, Bool.false_eq_true, and_false,
    if_false, he, Finset.union_empty, defectTotal, Rat.cast_sum, apply_ite, Rat.cast_zero]
  apply Finset.sum_congr rfl
  intro state _
  simp only [doubled_completion_iff σ k hk t ht state]

/-- INTERNAL: Every terminal clique vertex respects the original partial
assignment: all displayed holes belong to its unassigned pairs.
TEXLINE: main.tex:818-826 -/
theorem conditional_leaf_respects {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (choices : Fin n → Bool) (R : PairedSet n)
    (hR : R = {(k, false), (k, true)} ∪
      (ordinarySlots σ k).image (fun t => (t, choices t))) (hole : R) :
    Respects σ (LeafCliqueFlow.leafVertex (fixedLabels σ) R hole) := by
  classical
  have hnone : ∀ e ∈ R, σ e.1 = none := by
    intro e he
    rw [hR] at he
    rcases Finset.mem_union.mp he with he | he
    · rcases Finset.mem_insert.mp he with rfl | he
      · exact hk
      · have heq := Finset.mem_singleton.mp he
        subst e
        exact hk
    · obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp he
      exact ((mem_ordinary_slots σ k t).mp ht).1
  intro i b hb
  constructor
  · exact Finset.mem_union_left _ ((mem_fixed_labels σ i b).mpr hb)
  · have hmateB : (i, !b) ∉ fixedLabels σ := by
      rw [mem_fixed_labels, hb]
      cases b <;> simp
    have hmateR : (i, !b) ∉ R := by
      intro hm
      have he := hnone (i, !b) hm
      rw [hb] at he
      cases he
    simp [LeafCliqueFlow.leafVertex, hmateB, hmateR]

end CountingMatroid.Analysis.ConditionalTransversalSlots

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · exact root completion/total and doubled-slot defect-coefficient bridges, root admissibility, terminal hole-set shape, and assignment-respecting terminal vertices. All declarations are proved without new assumptions.
-/
