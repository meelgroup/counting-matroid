import CountingMatroid.Analysis.DefectSlotSplitSignature
import CountingMatroid.Analysis.DefectSlotConservation

set_option autoImplicit false

/-!
Demand nodes and the binary recursion from the transport proof. Splitting a
node keeps old-hole values and assigns the new hole the value that balances
its child. The recursion records all leaves in processing order.
-/

namespace CountingMatroid.Analysis.SlotDemandRecursion

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

/-- INTERNAL: The displayed holes and their demand per unit weight at a
node of the analytical recursion.
TEXLINE: main.tex:516-530 -/
structure DemandNode (n : ℕ) where
  holes : PairedSet n
  values : PairedGround n → ℝ

/-- PAPER: main.tex:543-553
Keep every old-hole value and give the new hole the unique balancing value. -/
noncomputable def splitNode {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (c : Bool) : DemandNode n := by
  classical
  let R := insert (t, c) node.holes
  let s := slotTotal r o₁ o₂ q B R (U.erase t)
  exact ⟨R, Function.update node.values (t, c)
    (-(∑ i ∈ node.holes, s i * node.values i) / s (t, c))⟩

/-- INTERNAL: Demand balance is expressed using the completion totals at
the current node, before any further pair is processed.
TEXLINE: main.tex:528-530 -/
def Balanced {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n)) (node : DemandNode n) : Prop :=
  (∑ i ∈ node.holes, slotTotal r o₁ o₂ q B node.holes U i * node.values i) = 0

/-- INTERNAL: Old holes retain their values in both children.
TEXLINE: main.tex:543-553 -/
theorem split_node_keeps {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (c : Bool) (hfree : (t, c) ∉ node.holes)
    (i : PairedGround n) (hi : i ∈ node.holes) :
    (splitNode r o₁ o₂ q B U node t c).values i = node.values i := by
  classical
  have hne : i ≠ (t, c) := by rintro rfl; exact hfree hi
  exact Function.update_of_ne hne _ _

/-- PAPER: main.tex:548-553
Each child is balanced, using positivity of its new-hole total. -/
theorem split_node_balanced {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (c : Bool) (hfree : (t, c) ∉ node.holes) :
    Balanced r o₁ o₂ q B (U.erase t) (splitNode r o₁ o₂ q B U node t c) := by
  classical
  let s := slotTotal r o₁ o₂ q B (insert (t, c) node.holes) (U.erase t)
  have hu : 0 < s (t, c) := slot_total_pos r o₁ o₂ q hq B _ _ _
  unfold Balanced
  change (∑ i ∈ insert (t, c) node.holes, s i *
    (splitNode r o₁ o₂ q B U node t c).values i) = 0
  rw [Finset.sum_insert hfree]
  have hnew : (splitNode r o₁ o₂ q B U node t c).values (t, c) =
      -(∑ i ∈ node.holes, s i * node.values i) / s (t, c) := by
    exact Function.update_self _ _ _
  have hold : (∑ i ∈ node.holes, s i *
      (splitNode r o₁ o₂ q B U node t c).values i) =
      ∑ i ∈ node.holes, s i * node.values i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [split_node_keeps r o₁ o₂ q B U node t c hfree i hi]
  rw [hnew, hold, mul_div_cancel₀ _ hu.ne']
  ring

/-- PAPER: main.tex:516-520,642-665
Process the ordinary pairs in order and retain the displayed holes and
balanced demands at all terminal nodes. -/
noncomputable def leafNodes {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) : List (Fin n) → DemandNode n → List (DemandNode n)
  | [], node => [node]
  | t :: slots, node =>
    leafNodes r o₁ o₂ q B slots
      (splitNode r o₁ o₂ q B (t :: slots).toFinset node t false) ++
    leafNodes r o₁ o₂ q B slots
      (splitNode r o₁ o₂ q B (t :: slots).toFinset node t true)

/-- INTERNAL: A fresh split leaves every later pair fresh, using the
absence of repetitions in the processing order.
TEXLINE: main.tex:516-553 -/
private theorem split_tail_free {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (node : DemandNode n) (t : Fin n)
    (slots : List (Fin n)) (ht : t ∉ slots)
    (hfree : ∀ s ∈ t :: slots, ∀ c : Bool, (s, c) ∉ node.holes) (c : Bool) :
    ∀ s ∈ slots, ∀ d : Bool,
      (s, d) ∉ (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c).holes := by
  classical
  intro s hs d
  have hst : s ≠ t := by rintro rfl; exact ht hs
  change (s, d) ∉ insert (t, c) node.holes
  simp only [Finset.mem_insert, Prod.mk.injEq, not_or]
  exact ⟨fun h => hst h.1, hfree s (List.mem_cons_of_mem t hs) d⟩

/-- PAPER: main.tex:528-553,670-674
The recursive assignment is balanced at every leaf. The processing order
has no repeated pairs and all its labels are fresh at the starting node. -/
theorem leaf_nodes_balanced {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n)
    (slots : List (Fin n)) (hnodup : slots.Nodup) (node : DemandNode n)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ node.holes)
    (hbalance : Balanced r o₁ o₂ q B slots.toFinset node)
    (leaf : DemandNode n) (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots node) :
    Balanced r o₁ o₂ q B ∅ leaf := by
  classical
  induction slots generalizing node with
  | nil =>
    have heq : leaf = node := by simpa only [leafNodes, List.mem_singleton] using hleaf
    subst leaf
    exact hbalance
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    have hft (c : Bool) : (t, c) ∉ node.holes :=
      hfree t List.mem_cons_self c
    have herase : (t :: slots).toFinset.erase t = slots.toFinset := by
      rw [List.toFinset_cons, Finset.erase_insert (by simpa using ht)]
    have hbal (c : Bool) : Balanced r o₁ o₂ q B slots.toFinset
        (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c) := by
      rw [← herase]
      exact split_node_balanced r o₁ o₂ q hq B _ node t c (hft c)
    rcases List.mem_append.mp hleaf with ha | hb
    · exact ih hnd _ (split_tail_free r o₁ o₂ q B node t slots ht hfree false)
        (hbal false) ha
    · exact ih hnd _ (split_tail_free r o₁ o₂ q B node t slots ht hfree true)
        (hbal true) hb

/-- PAPER: main.tex:684-688
Every original hole retains its root demand value throughout the recursion. -/
theorem leaf_nodes_keep {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (hnodup : slots.Nodup)
    (node : DemandNode n)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ node.holes)
    (leaf : DemandNode n) (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots node) :
    ∀ i ∈ node.holes, i ∈ leaf.holes ∧ leaf.values i = node.values i := by
  classical
  induction slots generalizing node with
  | nil =>
    have heq : leaf = node := by simpa only [leafNodes, List.mem_singleton] using hleaf
    subst leaf
    intro i hi
    exact ⟨hi, rfl⟩
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    have hft (c : Bool) : (t, c) ∉ node.holes :=
      hfree t List.mem_cons_self c
    have child (c : Bool) (hleaf : leaf ∈ leafNodes r o₁ o₂ q B slots
        (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c)) :
        ∀ i ∈ node.holes, i ∈ leaf.holes ∧ leaf.values i = node.values i := by
      intro i hi
      have hmem : i ∈ (splitNode r o₁ o₂ q B (t :: slots).toFinset node t c).holes :=
        Finset.mem_insert_of_mem hi
      obtain ⟨hleafmem, hval⟩ := ih hnd _
        (split_tail_free r o₁ o₂ q B node t slots ht hfree c) hleaf i hmem
      exact ⟨hleafmem, hval.trans
        (split_node_keeps r o₁ o₂ q B _ node t c (hft c) i hi)⟩
    rcases List.mem_append.mp hleaf with ha | hb
    · exact child false ha
    · exact child true hb

/-- INTERNAL: The recursion always has at least one leaf, including when
there are no ordinary pairs to process.
TEXLINE: main.tex:708-709 -/
theorem leaf_nodes_nonempty {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (slots : List (Fin n)) (node : DemandNode n) :
    ∃ leaf, leaf ∈ leafNodes r o₁ o₂ q B slots node := by
  induction slots generalizing node with
  | nil => exact ⟨node, by simp [leafNodes]⟩
  | cons t slots ih =>
    obtain ⟨leaf, hleaf⟩ := ih (splitNode r o₁ o₂ q B (t :: slots).toFinset node t false)
    exact ⟨leaf, List.mem_append_left _ hleaf⟩

/-- PAPER: main.tex:553
The two newly introduced values are opposite whenever the parent is
balanced; the denominator is the same in the two children. -/
theorem split_nodes_opposite {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (ht : t ∈ U)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hbalance : Balanced r o₁ o₂ q B U node) :
    (splitNode r o₁ o₂ q B U node t false).values (t, false) +
      (splitNode r o₁ o₂ q B U node t true).values (t, true) = 0 := by
  classical
  let sₐ := slotTotal r o₁ o₂ q B (insert (t, false) node.holes) (U.erase t)
  let sᵦ := slotTotal r o₁ o₂ q B (insert (t, true) node.holes) (U.erase t)
  have hsum : (∑ i ∈ node.holes, sₐ i * node.values i) +
      (∑ i ∈ node.holes, sᵦ i * node.values i) = 0 := by
    rw [← Finset.sum_add_distrib]
    calc
      _ = ∑ i ∈ node.holes, slotTotal r o₁ o₂ q B node.holes U i * node.values i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [← add_mul, DefectSlotConservation.slot_total_split
          r o₁ o₂ q B node.holes U t ht hfree i hi]
      _ = 0 := hbalance
  have hu : sₐ (t, false) = sᵦ (t, true) :=
    DefectSlotConservation.new_hole_total_eq r o₁ o₂ q B node.holes U t
      (fun c => (hfree c).2)
  change Function.update node.values (t, false) _ (t, false) +
    Function.update node.values (t, true) _ (t, true) = 0
  rw [Function.update_self, Function.update_self]
  change -(∑ i ∈ node.holes, sₐ i * node.values i) / sₐ (t, false) +
    -(∑ i ∈ node.holes, sᵦ i * node.values i) / sᵦ (t, true) = 0
  rw [← hu, ← add_div, ← neg_add, hsum, neg_zero, zero_div]

/-- PAPER: main.tex:555-560
Potential of one demand node, with the current completion totals and the
multiplier of each displayed hole. -/
noncomputable def nodePotential {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (W : PairedGround n → ℝ) (node : DemandNode n) : ℝ :=
  ∑ i ∈ node.holes, slotTotal r o₁ o₂ q B node.holes U i * node.values i ^ 2 / W i

/-- INTERNAL: The future quadratic evaluated at a demand node.
TEXLINE: main.tex:628-641 -/
noncomputable def nodeFuture {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (s : Fin n) : ℝ :=
  ∑ i ∈ node.holes, ∑ j ∈ node.holes,
    futureMatrix r o₁ o₂ q B node.holes U s i j * node.values i * node.values j

/-- PAPER: main.tex:628-641
The concrete split operation conserves every future-slot quadratic. -/
theorem split_future_conserved {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t s : Fin n) (ht : t ∈ U) (hts : t ≠ s)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hbalance : Balanced r o₁ o₂ q B U node) :
    nodeFuture r o₁ o₂ q B (U.erase t) (splitNode r o₁ o₂ q B U node t false) s +
      nodeFuture r o₁ o₂ q B (U.erase t) (splitNode r o₁ o₂ q B U node t true) s =
        nodeFuture r o₁ o₂ q B U node s := by
  exact DefectSlotConservation.future_form_conserved r o₁ o₂ q B node.holes U t s
    ht hts hfree node.values
    (splitNode r o₁ o₂ q B U node t false).values
    (splitNode r o₁ o₂ q B U node t true).values
    (split_node_keeps r o₁ o₂ q B U node t false (hfree false).2)
    (split_node_keeps r o₁ o₂ q B U node t true (hfree true).2)
    (split_nodes_opposite r o₁ o₂ q B U node t ht hfree hbalance)

/-- PAPER: main.tex:563-567,642-647
The concrete demand split increases the potential by at most the negated
future quadratic divided by the processed pair's multiplier. -/
theorem split_potential_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (U : Finset (Fin n))
    (node : DemandNode n) (t : Fin n) (ht : t ∈ U)
    (hBR : Disjoint B node.holes)
    (hfree : ∀ s ∈ U, ∀ c : Bool, (s, c) ∉ B ∧ (s, c) ∉ node.holes)
    (hsize : B.card + node.holes.card + U.card = n + 1)
    (hbalance : Balanced r o₁ o₂ q B U node)
    (W : PairedGround n → ℝ) (hW : W (t, false) = W (t, true))
    (hWpos : 0 < W (t, false)) (hsplit : SlotSplitControl n r o₁ o₂ q) :
    nodePotential r o₁ o₂ q B (U.erase t) W (splitNode r o₁ o₂ q B U node t false) +
      nodePotential r o₁ o₂ q B (U.erase t) W (splitNode r o₁ o₂ q B U node t true) ≤
    nodePotential r o₁ o₂ q B U W node - nodeFuture r o₁ o₂ q B U node t / W (t, false) := by
  classical
  let sₐ := slotTotal r o₁ o₂ q B (insert (t, false) node.holes) (U.erase t)
  let sᵦ := slotTotal r o₁ o₂ q B (insert (t, true) node.holes) (U.erase t)
  let u := sₐ (t, false)
  let X := ∑ i ∈ node.holes, sₐ i * node.values i
  have hu : 0 < u := slot_total_pos r o₁ o₂ q hq B _ _ _
  have hbal : (∑ i ∈ node.holes, (sₐ i + sᵦ i) * node.values i) = 0 := by
    calc
      _ = ∑ i ∈ node.holes, slotTotal r o₁ o₂ q B node.holes U i * node.values i := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [DefectSlotConservation.slot_total_split r o₁ o₂ q B node.holes U
          t ht (hfree t ht) i hi]
      _ = 0 := hbalance
  have hbnd : 2 * X ^ 2 / u ≤ -nodeFuture r o₁ o₂ q B U node t :=
    hsplit B node.holes U hBR hfree hsize t ht node.values hbal
  let hₐ := (splitNode r o₁ o₂ q B U node t false).values
  let hᵦ := (splitNode r o₁ o₂ q B U node t true).values
  have hval : hₐ (t, false) = -X / u := by
    exact Function.update_self _ _ _
  have hopp : hᵦ (t, true) = -hₐ (t, false) := by
    have hh := split_nodes_opposite r o₁ o₂ q B U node t ht (hfree t ht) hbalance
    change hₐ (t, false) + hᵦ (t, true) = 0 at hh
    linarith
  have hcost : u * hₐ (t, false) ^ 2 + u * hᵦ (t, true) ^ 2 = 2 * X ^ 2 / u := by
    rw [hopp, hval]
    field_simp
    ring
  have hpot := DefectSlotConservation.slot_potential_split r o₁ o₂ q B node.holes U t
    ht (hfree t ht) W node.values hₐ hᵦ
    (split_node_keeps r o₁ o₂ q B U node t false (hfree t ht false).2)
    (split_node_keeps r o₁ o₂ q B U node t true (hfree t ht true).2) hW
  change nodePotential r o₁ o₂ q B (U.erase t) W (splitNode r o₁ o₂ q B U node t false) +
    nodePotential r o₁ o₂ q B (U.erase t) W (splitNode r o₁ o₂ q B U node t true) =
    nodePotential r o₁ o₂ q B U W node +
      (u * hₐ (t, false) ^ 2 + u * hᵦ (t, true) ^ 2) / W (t, false) at hpot
  rw [hpot, hcost]
  have hdiv := div_le_div_of_nonneg_right hbnd hWpos.le
  rw [neg_div] at hdiv
  linarith

/-- PAPER: main.tex:642-665
Iterating the balanced splits bounds the total leaf potential by the root
potential minus the sum of its future-slot quadratics. This is the recursive
potential estimate before the root's two-hole data are substituted. -/
theorem leaf_potential_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n)
    (slots : List (Fin n)) (hnodup : slots.Nodup) (node : DemandNode n)
    (hBR : Disjoint B node.holes)
    (hfree : ∀ s ∈ slots, ∀ c : Bool, (s, c) ∉ B ∧ (s, c) ∉ node.holes)
    (hsize : B.card + node.holes.card + slots.toFinset.card = n + 1)
    (hbalance : Balanced r o₁ o₂ q B slots.toFinset node)
    (W : PairedGround n → ℝ)
    (hW : ∀ s ∈ slots, W (s, false) = W (s, true) ∧ 0 < W (s, false))
    (hsplit : SlotSplitControl n r o₁ o₂ q) :
    ((leafNodes r o₁ o₂ q B slots node).map (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
      nodePotential r o₁ o₂ q B slots.toFinset W node -
        ∑ s ∈ slots.toFinset, nodeFuture r o₁ o₂ q B slots.toFinset node s / W (s, false) := by
  classical
  induction slots generalizing node with
  | nil =>
    simp only [leafNodes, List.map_singleton, List.sum_singleton,
      List.toFinset_nil, Finset.sum_empty, sub_zero, le_refl]
  | cons t slots ih =>
    obtain ⟨ht, hnd⟩ := List.nodup_cons.mp hnodup
    let U := (t :: slots).toFinset
    let V := slots.toFinset
    have hUe : U = insert t V := List.toFinset_cons
    let N := fun c => splitNode r o₁ o₂ q B U node t c
    have htV : t ∉ V := by simpa only [V, List.mem_toFinset] using ht
    have htU : t ∈ U := by simp only [U, List.toFinset_cons, Finset.mem_insert, true_or]
    have herase : U.erase t = V := by
      rw [hUe, Finset.erase_insert htV]
    have hft (c : Bool) : (t, c) ∉ B ∧ (t, c) ∉ node.holes :=
      hfree t List.mem_cons_self c
    have hchildBR (c : Bool) : Disjoint B (N c).holes := by
      change Disjoint B (insert (t, c) node.holes)
      rw [Finset.disjoint_insert_right]
      exact ⟨hft c |>.1, hBR⟩
    have hchildFree (c : Bool) : ∀ s ∈ slots, ∀ d : Bool,
        (s, d) ∉ B ∧ (s, d) ∉ (N c).holes := by
      intro s hs d
      exact ⟨(hfree s (List.mem_cons_of_mem t hs) d).1,
        split_tail_free r o₁ o₂ q B node t slots ht
          (fun s hs d => (hfree s hs d).2) c s hs d⟩
    have hchildSize (c : Bool) : B.card + (N c).holes.card + V.card = n + 1 := by
      have hUcard : U.card = V.card + 1 := by
        rw [hUe, Finset.card_insert_of_notMem htV]
      have hRcard : (N c).holes.card = node.holes.card + 1 :=
        Finset.card_insert_of_notMem (hft c).2
      change B.card + node.holes.card + U.card = n + 1 at hsize
      omega
    have hchildBal (c : Bool) : Balanced r o₁ o₂ q B V (N c) := by
      rw [← herase]
      exact split_node_balanced r o₁ o₂ q hq B U node t c (hft c).2
    have hWTail : ∀ s ∈ slots, W (s, false) = W (s, true) ∧ 0 < W (s, false) :=
      fun s hs => hW s (List.mem_cons_of_mem t hs)
    have hrec (c : Bool) := ih hnd (N c) (hchildBR c) (hchildFree c)
      (hchildSize c) (hchildBal c) hWTail
    have hbound := split_potential_bound r o₁ o₂ q hq B U node t htU hBR
      (fun s hs d => hfree s (List.mem_toFinset.mp hs) d) hsize hbalance W
      (hW t List.mem_cons_self).1 (hW t List.mem_cons_self).2 hsplit
    rw [herase] at hbound
    have hfutureSum :
        (∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N false) s / W (s, false)) +
        (∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N true) s / W (s, false)) =
          ∑ s ∈ V, nodeFuture r o₁ o₂ q B U node s / W (s, false) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro s hs
      rw [← add_div]
      have hts : t ≠ s := by rintro rfl; exact htV hs
      have hc := split_future_conserved r o₁ o₂ q B U node t s htU hts hft hbalance
      rw [herase] at hc
      rw [hc]
    have hrootSum :
        (∑ s ∈ U, nodeFuture r o₁ o₂ q B U node s / W (s, false)) =
        nodeFuture r o₁ o₂ q B U node t / W (t, false) +
          ∑ s ∈ V, nodeFuture r o₁ o₂ q B U node s / W (s, false) := by
      rw [hUe, Finset.sum_insert htV]
    rw [leafNodes, List.map_append, List.sum_append]
    change _ ≤ nodePotential r o₁ o₂ q B U W node -
      ∑ s ∈ U, nodeFuture r o₁ o₂ q B U node s / W (s, false)
    rw [hrootSum]
    have ha := hrec false
    have hb := hrec true
    change ((leafNodes r o₁ o₂ q B slots (N false)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
      nodePotential r o₁ o₂ q B V W (N false) -
        ∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N false) s / W (s, false) at ha
    change ((leafNodes r o₁ o₂ q B slots (N true)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
      nodePotential r o₁ o₂ q B V W (N true) -
        ∑ s ∈ V, nodeFuture r o₁ o₂ q B V (N true) s / W (s, false) at hb
    change nodePotential r o₁ o₂ q B V W (N false) +
      nodePotential r o₁ o₂ q B V W (N true) ≤
      nodePotential r o₁ o₂ q B U W node - nodeFuture r o₁ o₂ q B U node t / W (t, false)
      at hbound
    change ((leafNodes r o₁ o₂ q B slots (N false)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum +
      ((leafNodes r o₁ o₂ q B slots (N true)).map
      (nodePotential r o₁ o₂ q B ∅ W)).sum ≤ _
    linarith [ha, hb, hbound, hfutureSum]

/-- PAPER: main.tex:531
Initialize the two root holes with opposite unit total demands. -/
noncomputable def twoHoleRoot {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n) : DemandNode n := by
  classical
  let R : PairedSet n := {p, d}
  let s := slotTotal r o₁ o₂ q B R U
  exact ⟨R, fun i => if i = p then 1 / s p else if i = d then -1 / s d else 0⟩

/-- PAPER: main.tex:528-531
The two unit root demands balance under the positive completion totals. -/
theorem two_hole_root_balanced {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n) (hpd : p ≠ d) :
    Balanced r o₁ o₂ q B U (twoHoleRoot r o₁ o₂ q B U p d) := by
  classical
  let s := slotTotal r o₁ o₂ q B ({p, d} : PairedSet n) U
  have hp : 0 < s p := slot_total_pos r o₁ o₂ q hq B _ _ _
  have hd : 0 < s d := slot_total_pos r o₁ o₂ q hq B _ _ _
  change (∑ i ∈ ({p, d} : PairedSet n), s i *
    (if i = p then 1 / s p else if i = d then -1 / s d else 0)) = 0
  rw [Finset.sum_insert (by simpa using hpd), Finset.sum_singleton]
  simp only [ite_true, if_neg (Ne.symm hpd)]
  rw [mul_div_cancel₀ _ hp.ne', mul_div_cancel₀ _ hd.ne']
  norm_num

/-- INTERNAL: The proved demand-tree interface needed by leaf-flow
assembly, including balance, persistent root values, and the total cost.
TEXLINE: main.tex:516-665 -/
structure DemandRecursionControl (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) : Prop where
  root_balanced : ∀ (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n), p ≠ d →
    Balanced r o₁ o₂ q B U (twoHoleRoot r o₁ o₂ q B U p d)
  tree : ∀ (B : PairedSet n) (slots : List (Fin n)), slots.Nodup →
    ∀ node : DemandNode n, Disjoint B node.holes →
    (∀ s ∈ slots, ∀ c : Bool, (s, c) ∉ B ∧ (s, c) ∉ node.holes) →
    B.card + node.holes.card + slots.toFinset.card = n + 1 →
    Balanced r o₁ o₂ q B slots.toFinset node →
    ∀ W : PairedGround n → ℝ,
    (∀ s ∈ slots, W (s, false) = W (s, true) ∧ 0 < W (s, false)) →
    ∃ leaves : List (DemandNode n),
      (∃ leaf, leaf ∈ leaves) ∧
      (∀ leaf ∈ leaves, Balanced r o₁ o₂ q B ∅ leaf) ∧
      (∀ leaf ∈ leaves, ∀ i ∈ node.holes,
        i ∈ leaf.holes ∧ leaf.values i = node.values i) ∧
      (leaves.map (nodePotential r o₁ o₂ q B ∅ W)).sum ≤
        nodePotential r o₁ o₂ q B slots.toFinset W node -
          ∑ s ∈ slots.toFinset,
            nodeFuture r o₁ o₂ q B slots.toFinset node s / W (s, false)

/-- INTERNAL: The recursive demand construction satisfies the whole
leaf-demand interface when the imported all-node signature split bound holds.
TEXLINE: main.tex:516-665 -/
theorem demand_recursion_control (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (hsplit : SlotSplitControl n r o₁ o₂ q) :
    DemandRecursionControl n r o₁ o₂ q := by
  refine ⟨two_hole_root_balanced r o₁ o₂ q hq, ?_⟩
  intro B slots hnodup node hBR hfree hsize hbalance W hW
  refine ⟨leafNodes r o₁ o₂ q B slots node,
    leaf_nodes_nonempty r o₁ o₂ q B slots node, ?_, ?_, ?_⟩
  · exact leaf_nodes_balanced r o₁ o₂ q hq B slots hnodup node
      (fun s hs c => (hfree s hs c).2) hbalance
  · exact leaf_nodes_keep r o₁ o₂ q B slots hnodup node
      (fun s hs c => (hfree s hs c).2)
  · exact leaf_potential_bound r o₁ o₂ q hq B slots hnodup node hBR hfree hsize
      hbalance W hW hsplit

end CountingMatroid.Analysis.SlotDemandRecursion
