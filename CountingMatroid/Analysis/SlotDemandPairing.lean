import CountingMatroid.Analysis.SlotDemandRecursion

set_option autoImplicit false

/-!
First-moment conservation for the paper's balanced demand recursion.
The same completion partition works for an arbitrary state function, so
opposite new-hole demands cancel before any exchange flow is constructed.
-/

namespace CountingMatroid.Analysis.SlotDemandPairing

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open scoped BigOperators

/-- INTERNAL: A completion sum with an arbitrary state function, including
weighted potential values and pointwise indicators.
TEXLINE: main.tex:535-553,684-692 -/
noncomputable def completionMoment {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (hole : PairedGround n) (f : PairedSet n → ℝ) : ℝ := by
  classical
  exact ∑ state, if SlotCompletion B R U hole state then f state else 0

/-- INTERNAL: Removing a displayed old hole partitions its completions
according to the bit selected at the next free pair.
TEXLINE: main.tex:535-540 -/
theorem completion_partition {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (ht : t ∈ U)
    (hole : PairedGround n) (hhole : hole ∈ R)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (state : PairedSet n) :
    SlotCompletion B R U hole state ↔
      SlotCompletion B (insert (t, false) R) (U.erase t) hole state ∨
      SlotCompletion B (insert (t, true) R) (U.erase t) hole state := by
  classical
  have hne (c : Bool) : (t, c) ≠ hole := by
    rintro rfl
    exact (hfree c).2 hhole
  have himage (choices : Fin n → Bool) : U.image (fun s => (s, choices s)) =
      insert (t, choices t) ((U.erase t).image (fun s => (s, choices s))) := by
    conv_lhs => rw [← Finset.insert_erase ht, Finset.image_insert]
  constructor
  · rintro ⟨choices, rfl⟩
    rw [himage]
    cases choices t with
    | false =>
      left
      refine ⟨choices, ?_⟩
      simp only [Finset.erase_insert_of_ne (hne false), Finset.union_insert, Finset.insert_union]
    | true =>
      right
      refine ⟨choices, ?_⟩
      simp only [Finset.erase_insert_of_ne (hne true), Finset.union_insert, Finset.insert_union]
  · have lift (c : Bool) (choices : Fin n → Bool)
        (hs : state = B ∪ (insert (t, c) R).erase hole ∪
          (U.erase t).image (fun s => (s, choices s))) :
        SlotCompletion B R U hole state := by
      refine ⟨Function.update choices t c, ?_⟩
      have he : (U.erase t).image (fun s => (s, Function.update choices t c s)) =
          (U.erase t).image (fun s => (s, choices s)) := by
        apply Finset.image_congr
        intro s hs
        dsimp only
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
      rw [himage, Function.update_self, he]
      simpa only [Finset.erase_insert_of_ne (hne c), Finset.union_insert, Finset.insert_union] using hs
    rintro (⟨choices, hs⟩ | ⟨choices, hs⟩)
    · exact lift false choices hs
    · exact lift true choices hs

/-- INTERNAL: An old-hole child completion contains precisely the selected
bit of the processed pair.
TEXLINE: main.tex:535-540 -/
theorem completion_child_bit {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (hole : PairedGround n)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (c d : Bool) (state : PairedSet n)
    (hs : SlotCompletion B (insert (t, c) R) (U.erase t) hole state)
    (hne : (t, c) ≠ hole) : (t, d) ∈ state ↔ d = c := by
  classical
  obtain ⟨choices, rfl⟩ := hs
  have hn : (t, d) ∉ (U.erase t).image (fun s => (s, choices s)) := by
    intro hm
    obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hm
    exact (Finset.ne_of_mem_erase hs) (congrArg Prod.fst he)
  simp [Finset.erase_insert_of_ne hne, (hfree d).1, (hfree d).2, hn]

/-- INTERNAL: The binary partition preserves every completion moment,
not just the unweighted total.
TEXLINE: main.tex:535-540,684-692 -/
theorem completion_moment_split {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (ht : t ∈ U)
    (hole : PairedGround n) (hhole : hole ∈ R)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (f : PairedSet n → ℝ) :
    completionMoment B (insert (t, false) R) (U.erase t) hole f +
      completionMoment B (insert (t, true) R) (U.erase t) hole f =
        completionMoment B R U hole f := by
  classical
  unfold completionMoment
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state _
  have hdis : SlotCompletion B (insert (t, false) R) (U.erase t) hole state →
      ¬ SlotCompletion B (insert (t, true) R) (U.erase t) hole state := by
    intro ha hb
    have hne (c : Bool) : (t, c) ≠ hole := by
      rintro rfl
      exact (hfree c).2 hhole
    have hm := (completion_child_bit B R U t hole hfree false false state ha (hne false)).mpr rfl
    have hf := (completion_child_bit B R U t hole hfree true false state hb (hne true)).mp hm
    cases hf
  rw [completion_partition B R U t ht hole hhole hfree]
  by_cases ha : SlotCompletion B (insert (t, false) R) (U.erase t) hole state
  · rw [if_pos ha, if_neg (hdis ha), if_pos (Or.inl ha), add_zero]
  · by_cases hb : SlotCompletion B (insert (t, true) R) (U.erase t) hole state
    · rw [if_neg ha, if_pos hb, if_pos (Or.inr hb), zero_add]
    · rw [if_neg ha, if_neg hb, if_neg (not_or.mpr ⟨ha, hb⟩), zero_add]

/-- PAPER: main.tex:540-543,689-692
The new-hole completion moments coincide for both choices, since the
processed pair is empty in their shared state. -/
theorem new_hole_moment_eq {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n)
    (hfree : ∀ c : Bool, (t, c) ∉ R) (f : PairedSet n → ℝ) :
    completionMoment B (insert (t, false) R) (U.erase t) (t, false) f =
      completionMoment B (insert (t, true) R) (U.erase t) (t, true) f := by
  classical
  simp only [completionMoment, SlotCompletion, Finset.erase_insert (hfree _)]

/-- INTERNAL: Pair a demand node with any state function. Taking the state
function to be rank weight times a potential yields the transport pairing.
TEXLINE: main.tex:499-507,684-692 -/
noncomputable def nodePairing {n : ℕ} (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (f : PairedSet n → ℝ) : ℝ :=
  ∑ i ∈ node.holes, node.values i * completionMoment B node.holes U i f

/-- PAPER: main.tex:684-692
A balanced split preserves the pairing: old-hole moments partition, while
the two opposite new-hole values multiply the same shared-state moment. -/
theorem split_pairing_conserved {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n)) (node : DemandNode n)
    (t : Fin n) (ht : t ∈ U)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hbalance : Balanced r o₁ o₂ q B U node) (f : PairedSet n → ℝ) :
    nodePairing B (U.erase t) (splitNode r o₁ o₂ q B U node t false) f +
      nodePairing B (U.erase t) (splitNode r o₁ o₂ q B U node t true) f =
        nodePairing B U node f := by
  classical
  let N := fun c => splitNode r o₁ o₂ q B U node t c
  change (∑ i ∈ insert (t, false) node.holes,
    (N false).values i * completionMoment B (N false).holes (U.erase t) i f) +
    (∑ i ∈ insert (t, true) node.holes,
    (N true).values i * completionMoment B (N true).holes (U.erase t) i f) = _
  rw [Finset.sum_insert (hfree false).2, Finset.sum_insert (hfree true).2]
  have hold : (∑ i ∈ node.holes,
      (N false).values i * completionMoment B (N false).holes (U.erase t) i f) +
      (∑ i ∈ node.holes,
      (N true).values i * completionMoment B (N true).holes (U.erase t) i f) =
      nodePairing B U node f := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [split_node_keeps r o₁ o₂ q B U node t false (hfree false).2 i hi,
      split_node_keeps r o₁ o₂ q B U node t true (hfree true).2 i hi, ← mul_add]
    exact congrArg (node.values i * ·)
      (completion_moment_split B node.holes U t ht i hi hfree f)
  have hnew := new_hole_moment_eq B node.holes U t (fun c => (hfree c).2) f
  have hopp := split_nodes_opposite r o₁ o₂ q B U node t ht hfree hbalance
  change (N false).values (t, false) + (N true).values (t, true) = 0 at hopp
  change completionMoment B (N false).holes (U.erase t) (t, false) f =
    completionMoment B (N true).holes (U.erase t) (t, true) f at hnew
  rw [← hnew]
  have hcancel : (N false).values (t, false) *
      completionMoment B (N false).holes (U.erase t) (t, false) f +
      (N true).values (t, true) *
      completionMoment B (N false).holes (U.erase t) (t, false) f = 0 := by
    rw [← add_mul, hopp, zero_mul]
  linarith

/-- PAPER: main.tex:684-709
Summing the terminal pairings recovers the root pairing, including exact
cancellation at every ordinary-hole state. No flow or edge enumeration is
needed for this first-moment identity. -/
theorem leaf_pairing_conserved {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (slots : List (Fin n))
    (hnodup : slots.Nodup) (node : DemandNode n)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hbalance : Balanced r o₁ o₂ q B slots.toFinset node)
    (f : PairedSet n → ℝ) :
    ((leafNodes r o₁ o₂ q B slots node).map (fun leaf => nodePairing B ∅ leaf f)).sum =
      nodePairing B slots.toFinset node f := by
  classical
  induction slots generalizing node with
  | nil => simp only [leafNodes, List.map_singleton, List.sum_singleton, List.toFinset_nil]
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    let U := (t :: slots).toFinset
    let N := fun c => splitNode r o₁ o₂ q B U node t c
    have herase : U.erase t = slots.toFinset := by
      dsimp only [U]
      rw [List.toFinset_cons, Finset.erase_insert (by simpa using ht)]
    have hft (c : Bool) : (t, c) ∉ B ∧ (t, c) ∉ node.holes :=
      hfree t List.mem_cons_self c
    have hchildFree (c : Bool) : ∀ s ∈ slots, ∀ d : Bool,
        (s, d) ∉ B ∧ (s, d) ∉ (N c).holes := by
      intro s hs d
      constructor
      · exact (hfree s (List.mem_cons_of_mem t hs) d).1
      · have hst : s ≠ t := by rintro rfl; exact ht hs
        change (s, d) ∉ insert (t, c) node.holes
        simp only [Finset.mem_insert, Prod.mk.injEq, not_or]
        exact ⟨fun he => hst he.1, (hfree s (List.mem_cons_of_mem t hs) d).2⟩
    have hchildBal (c : Bool) : Balanced r o₁ o₂ q B slots.toFinset (N c) := by
      rw [← herase]
      exact split_node_balanced r o₁ o₂ q hq B U node t c (hft c).2
    rw [leafNodes, List.map_append, List.sum_append]
    rw [ih hnd (N false) (hchildFree false) (hchildBal false),
      ih hnd (N true) (hchildFree true) (hchildBal true)]
    rw [← herase]
    exact split_pairing_conserved r o₁ o₂ q B U node t
      (by simp [U]) hft hbalance f

/-- INTERNAL: At a terminal node each hole has exactly one completion.
TEXLINE: main.tex:670-674 -/
theorem completion_moment_terminal {n : ℕ} (B R : PairedSet n)
    (hole : PairedGround n) (f : PairedSet n → ℝ) :
    completionMoment B R ∅ hole f = f (B ∪ R.erase hole) := by
  classical
  simp [completionMoment, SlotCompletion]

end CountingMatroid.Analysis.SlotDemandPairing
