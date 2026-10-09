import CountingMatroid.Analysis.SlotDemandRecursion

set_option autoImplicit false

/-!
Finite-set geometry of the balanced demand tree. Different binary branches
have different displayed hole sets; admissible nodes remain admissible at
all leaves. These facts account for disjoint exchange edges at the leaves.
-/

namespace CountingMatroid.Analysis.SlotLeafGeometry

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.SlotDemandRecursion

/-- INTERNAL: A label not initially displayed and not processed by the
remaining slots cannot appear at a descendant leaf.
TEXLINE: main.tex:516-520,681-683 -/
theorem leaf_holes_exclude {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (node : DemandNode n)
    (e : PairedGround n) (he : e ∉ node.holes) (hslots : e.1 ∉ slots)
    (leaf : DemandNode n) (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots node) :
    e ∉ leaf.holes := by
  classical
  induction slots generalizing node with
  | nil =>
    have hh : leaf = node := by simpa only [leafNodes, List.mem_singleton] using hleaf
    subst leaf
    exact he
  | cons t slots ih =>
    have het : e.1 ≠ t := fun hh => hslots (hh ▸ List.mem_cons_self)
    have heTail : e.1 ∉ slots := fun hh => hslots (List.mem_cons_of_mem t hh)
    have hchild (c : Bool) :
        e ∉ (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c).holes := by
      change e ∉ insert (t, c) node.holes
      simp only [Finset.mem_insert, not_or]
      exact ⟨fun hh => het (congrArg Prod.fst hh), he⟩
    rcases List.mem_append.mp hleaf with ha | hb
    · exact ih _ (hchild false) heTail ha
    · exact ih _ (hchild true) heTail hb

/-- INTERNAL: After a fresh pair is inserted, all later pairs are still
fresh if the processing list has no repetitions.
TEXLINE: main.tex:516-553 -/
private theorem child_free {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (node : DemandNode n)
    (t : Fin n) (ht : t ∉ slots)
    (hfree : ∀ s ∈ t :: slots, ∀ c : Bool, (s, c) ∉ B ∧ (s, c) ∉ node.holes)
    (c : Bool) : ∀ s ∈ slots, ∀ d : Bool,
      (s, d) ∉ B ∧
        (s, d) ∉ (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c).holes := by
  intro s hs d
  have hst : s ≠ t := by rintro rfl; exact ht hs
  refine ⟨(hfree s (List.mem_cons_of_mem t hs) d).1, ?_⟩
  change (s, d) ∉ insert (t, c) node.holes
  simp only [Finset.mem_insert, Prod.mk.injEq, not_or]
  exact ⟨fun hh => hst hh.1, (hfree s (List.mem_cons_of_mem t hs) d).2⟩

/-- PAPER: main.tex:681-683
Distinct leaves have distinct displayed hole sets. The two branches of a
processed pair can be distinguished by its selected bit at every descendant. -/
theorem leaf_holes_pairwise {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (hnodup : slots.Nodup)
    (node : DemandNode n)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes) :
    (leafNodes r o₁ o₂ q B slots node).Pairwise
      (fun left right => left.holes ≠ right.holes) := by
  classical
  induction slots generalizing node with
  | nil => simp [leafNodes]
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    let N := fun c => splitNode r o₁ o₂ q B (t :: slots).toFinset node t c
    rw [leafNodes, List.pairwise_append]
    refine ⟨ih hnd (N false) (child_free r o₁ o₂ q B slots node t ht hfree false),
      ih hnd (N true) (child_free r o₁ o₂ q B slots node t ht hfree true), ?_⟩
    intro left hl right hr heq
    have hleft : (t, false) ∈ left.holes := by
      have hkeep := leaf_nodes_keep r o₁ o₂ q B slots hnd (N false)
        (fun s hs d => (child_free r o₁ o₂ q B slots node t ht hfree false s hs d).2)
        left hl (t, false) (Finset.mem_insert_self _ _)
      exact hkeep.1
    have hright : (t, false) ∉ right.holes := by
      apply leaf_holes_exclude r o₁ o₂ q B slots (N true) (t, false) _ ht right hr
      change (t, false) ∉ insert (t, true) node.holes
      simp only [Finset.mem_insert, Prod.mk.injEq, Bool.false_eq_true, and_false, false_or]
      exact (hfree t List.mem_cons_self false).2
    exact hright (heq ▸ hleft)

/-- INTERNAL: Every leaf keeps the fixed selected labels disjoint from
its displayed holes.
TEXLINE: main.tex:516-520,670-674 -/
theorem leaf_holes_disjoint {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (node : DemandNode n)
    (hBR : Disjoint B node.holes)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ B)
    (leaf : DemandNode n) (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots node) :
    Disjoint B leaf.holes := by
  classical
  induction slots generalizing node with
  | nil =>
    have hh : leaf = node := by simpa only [leafNodes, List.mem_singleton] using hleaf
    subst leaf
    exact hBR
  | cons t slots ih =>
    have hchild (c : Bool) : Disjoint B
        (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c).holes := by
      change Disjoint B (insert (t, c) node.holes)
      rw [Finset.disjoint_insert_right]
      exact ⟨hfree t List.mem_cons_self c, hBR⟩
    have htail : ∀ s ∈ slots, ∀ c : Bool, (s, c) ∉ B :=
      fun s hs c => hfree s (List.mem_cons_of_mem t hs) c
    rcases List.mem_append.mp hleaf with ha | hb
    · exact ih _ (hchild false) htail ha
    · exact ih _ (hchild true) htail hb

/-- INTERNAL: A common disjoint fixed base can be cancelled from two
leaf unions when recovering their displayed hole sets.
TEXLINE: main.tex:681-683 -/
theorem disjoint_base_union_injective {n : ℕ} (B R S : PairedSet n)
    (hBR : Disjoint B R) (hBS : Disjoint B S) (hunion : B ∪ R = B ∪ S) : R = S := by
  rw [← Finset.union_sdiff_cancel_left hBR, hunion,
    Finset.union_sdiff_cancel_left hBS]

/-- INTERNAL: Every leaf displays the original holes and precisely one
chosen label from each processed ordinary pair.
TEXLINE: main.tex:516-520,670-674 -/
theorem leaf_holes_shape {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (hnodup : slots.Nodup)
    (node : DemandNode n) (leaf : DemandNode n)
    (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots node) :
    ∃ choices : Fin n → Bool,
      leaf.holes = node.holes ∪ slots.toFinset.image (fun t => (t, choices t)) := by
  classical
  induction slots generalizing node with
  | nil =>
    have hh : leaf = node := by simpa only [leafNodes, List.mem_singleton] using hleaf
    subst leaf
    exact ⟨fun _ => false, by simp⟩
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    let N := fun c => splitNode r o₁ o₂ q B (t :: slots).toFinset node t c
    have child (c : Bool) (hl : leaf ∈ leafNodes r o₁ o₂ q B slots (N c)) :
        ∃ choices : Fin n → Bool,
          leaf.holes = node.holes ∪ (t :: slots).toFinset.image (fun s => (s, choices s)) := by
      obtain ⟨choices, heq⟩ := ih hnd (N c) hl
      refine ⟨Function.update choices t c, ?_⟩
      have himage : slots.toFinset.image (fun s => (s, Function.update choices t c s)) =
          slots.toFinset.image (fun s => (s, choices s)) := by
        apply Finset.image_congr
        intro s hs
        have hst : s ≠ t := by rintro rfl; exact ht (List.mem_toFinset.mp hs)
        dsimp only
        rw [Function.update_of_ne hst]
      rw [List.toFinset_cons, Finset.image_insert, Function.update_self, himage]
      change leaf.holes = node.holes ∪ insert (t, c) _
      simpa only [N, splitNode, Finset.union_insert, Finset.insert_union] using heq
    rcases List.mem_append.mp hleaf with ha | hb
    · exact child false ha
    · exact child true hb

end CountingMatroid.Analysis.SlotLeafGeometry
