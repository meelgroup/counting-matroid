import CountingMatroid.Analysis.LeafCliqueFlow
import CountingMatroid.Analysis.SlotLeafGeometry
import CountingMatroid.Analysis.DisjointFlowSum

set_option autoImplicit false

/-!
Assemble the balanced binary demand tree into an exchange-supported flow.
The exact first-moment identity cancels ordinary-hole demands, while the
finite-set leaf geometry makes the energies additive. The conductance
hypothesis is local to the terminal cliques and is kept separate from the
operational defect/event specialization.
-/

namespace CountingMatroid.Analysis.SlotTransportFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing
open CountingMatroid.Analysis.LeafCliqueFlow

/-- INTERNAL: Pointwise demand at a node, expressed by pairing against a
weighted indicator of the state.
TEXLINE: main.tex:493-498,684-692 -/
noncomputable def completionDemand {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (B : PairedSet n)
    (U : Finset (Fin n)) (node : DemandNode n) (state : PairedSet n) : ℝ := by
  classical
  exact nodePairing B U node (fun S => if S = state then
    ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ S).val) : ℚ) : ℝ)
    else 0)

/-- INTERNAL: At a terminal node the embedded clique demand is precisely
the pointwise completion demand.
TEXLINE: main.tex:670-674,684-692 -/
theorem terminal_demand_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (node : DemandNode n) (state : PairedSet n) :
    (∑ hole : node.holes, if leafVertex B node.holes hole = state then
      slotTotal r o₁ o₂ q B node.holes ∅ hole * node.values hole else 0) =
        completionDemand r o₁ o₂ q B ∅ node state := by
  classical
  change (∑ hole : node.holes, if B ∪ node.holes.erase hole.val = state then
    slotTotal r o₁ o₂ q B node.holes ∅ hole * node.values hole else 0) = _
  rw [Finset.sum_coe_sort node.holes (fun hole => if B ∪ node.holes.erase hole = state then
    slotTotal r o₁ o₂ q B node.holes ∅ hole * node.values hole else 0)]
  unfold completionDemand nodePairing
  apply Finset.sum_congr rfl
  intro hole _
  rw [completion_moment_terminal]
  have hs : slotTotal r o₁ o₂ q B node.holes ∅ hole =
      ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
        (B ∪ node.holes.erase hole)).val) : ℚ) : ℝ) := by
    simp [slotTotal, SlotCompletion]
  rw [hs]
  split_ifs <;> ring

/-- PAPER: main.tex:670-709
The leaf stars assemble into a flow with the original balanced demand and
energy bounded by the iterated potential estimate. The local conductance
lower bound is the only input still needed from the operational chain. -/
theorem slot_transport_flow {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n)
    (slots : List (Fin n)) (hnodup : slots.Nodup) (node : DemandNode n)
    (hne : node.holes.Nonempty) (hBR : Disjoint B node.holes)
    (hfree : ∀ t ∈ slots, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ node.holes)
    (hsize : B.card + node.holes.card + slots.toFinset.card = n + 1)
    (hbalance : Balanced r o₁ o₂ q B slots.toFinset node)
    (W : PairedGround n → ℝ)
    (hWslots : ∀ t ∈ slots, W (t, false) = W (t, true) ∧ 0 < W (t, false))
    (hsplit : SlotSplitControl n r o₁ o₂ q)
    (κ : PairedSet n → PairedSet n → ℝ) (C : ℝ) (hC : 0 < C)
    (hsym : ∀ s t, κ s t = κ t s)
    (hWleaf : ∀ leaf ∈ leafNodes r o₁ o₂ q B slots node,
      ∀ i ∈ leaf.holes, 0 < W i)
    (hcap : ∀ leaf ∈ leafNodes r o₁ o₂ q B slots node,
      ∀ x y : leaf.holes, x ≠ y →
        min (W x * slotTotal r o₁ o₂ q B leaf.holes ∅ x)
          (W y * slotTotal r o₁ o₂ q B leaf.holes ∅ y) ≤
            C * κ (leafVertex B leaf.holes x) (leafVertex B leaf.holes y)) :
    ∃ flow : FlowCertificate κ (completionDemand r o₁ o₂ q B slots.toFinset node),
      flowEnergy κ flow.current ≤ C *
        (nodePotential r o₁ o₂ q B slots.toFinset W node -
          ∑ t ∈ slots.toFinset,
            nodeFuture r o₁ o₂ q B slots.toFinset node t / W (t, false)) := by
  classical
  let leaves := leafNodes r o₁ o₂ q B slots node
  have hleafBR : ∀ leaf ∈ leaves, Disjoint B leaf.holes :=
    SlotLeafGeometry.leaf_holes_disjoint r o₁ o₂ q B slots node hBR
      (fun t ht c => (hfree t ht c).1)
  have hflows : ∀ leaf ∈ leaves,
      ∃ flow : FlowCertificate κ (completionDemand r o₁ o₂ q B ∅ leaf),
        flowEnergy κ flow.current ≤ C * nodePotential r o₁ o₂ q B ∅ W leaf ∧
        (∀ s t, flow.current s t ≠ 0 → s ∪ t = B ∪ leaf.holes) := by
    intro leaf hl
    have hleafBalance := leaf_nodes_balanced r o₁ o₂ q hq B slots hnodup node
      (fun t ht c => (hfree t ht c).2) hbalance leaf hl
    obtain ⟨i, hi⟩ := hne
    have hkeep := leaf_nodes_keep r o₁ o₂ q B slots hnodup node
      (fun t ht c => (hfree t ht c).2) leaf hl i hi
    obtain ⟨flow, hcost, hunion⟩ := leaf_clique_flow r o₁ o₂ q hq B leaf
      (hleafBR leaf hl) ⟨i, hkeep.1⟩ hleafBalance W (hWleaf leaf hl) κ C hC
      hsym (hcap leaf hl)
    let adjusted : FlowCertificate κ (completionDemand r o₁ o₂ q B ∅ leaf) :=
      { current := flow.current
        antisymmetric := flow.antisymmetric
        supported := flow.supported
        divergence_eq := fun state => (flow.divergence_eq state).trans
          (terminal_demand_eq r o₁ o₂ q B leaf state) }
    exact ⟨adjusted, hcost, hunion⟩
  let J := fun leaf => if hl : leaf ∈ leaves then
    (Classical.choose (hflows leaf hl)).current else (fun _ _ => 0)
  have hanti : ∀ leaf ∈ leaves, ∀ s t, J leaf s t = -J leaf t s := by
    intro leaf hl s t
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose (hflows leaf hl)).antisymmetric s t
  have hsupport : ∀ leaf ∈ leaves, ∀ s t, κ s t = 0 → J leaf s t = 0 := by
    intro leaf hl s t hz
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose (hflows leaf hl)).supported s t hz
  have hdiv : ∀ leaf ∈ leaves, ∀ state,
      divergence (J leaf) state = completionDemand r o₁ o₂ q B ∅ leaf state := by
    intro leaf hl state
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose (hflows leaf hl)).divergence_eq state
  have hunion : ∀ leaf ∈ leaves, ∀ s t, J leaf s t ≠ 0 → s ∪ t = B ∪ leaf.holes := by
    intro leaf hl s t hz
    dsimp only [J] at hz
    rw [dif_pos hl] at hz
    exact (Classical.choose_spec (hflows leaf hl)).2 s t hz
  have hdisjoint : leaves.Pairwise (fun left right => ∀ s t, J left s t * J right s t = 0) := by
    apply List.Pairwise.imp_of_mem (p :=
      SlotLeafGeometry.leaf_holes_pairwise r o₁ o₂ q B slots hnodup node hfree)
    intro left right hl hr hne s t
    by_cases ha : J left s t = 0
    · rw [ha, zero_mul]
    by_cases hb : J right s t = 0
    · rw [hb, mul_zero]
    have heq : B ∪ left.holes = B ∪ right.holes :=
      (hunion left hl s t ha).symm.trans (hunion right hr s t hb)
    exact False.elim (hne (SlotLeafGeometry.disjoint_base_union_injective
      B left.holes right.holes (hleafBR left hl) (hleafBR right hr) heq))
  obtain ⟨flow, _, henergy⟩ := DisjointFlowSum.disjoint_flow_sum κ J
    (fun leaf => completionDemand r o₁ o₂ q B ∅ leaf) leaves hanti hsupport hdiv hdisjoint
  have hdemands : ∀ state,
      (leaves.map (fun leaf => completionDemand r o₁ o₂ q B ∅ leaf state)).sum =
        completionDemand r o₁ o₂ q B slots.toFinset node state := by
    intro state
    exact leaf_pairing_conserved r o₁ o₂ q hq B slots hnodup node hfree hbalance _
  let assembled : FlowCertificate κ (completionDemand r o₁ o₂ q B slots.toFinset node) :=
    { current := flow.current
      antisymmetric := flow.antisymmetric
      supported := flow.supported
      divergence_eq := fun state => (flow.divergence_eq state).trans (hdemands state) }
  refine ⟨assembled, henergy.trans_le ?_⟩
  have hleafCost : ∀ leaf ∈ leaves,
      flowEnergy κ (J leaf) ≤ C * nodePotential r o₁ o₂ q B ∅ W leaf := by
    intro leaf hl
    dsimp only [J]
    rw [dif_pos hl]
    exact (Classical.choose_spec (hflows leaf hl)).1
  calc
    _ ≤ (leaves.map (fun leaf => C * nodePotential r o₁ o₂ q B ∅ W leaf)).sum :=
      List.sum_le_sum hleafCost
    _ = C * (leaves.map (nodePotential r o₁ o₂ q B ∅ W)).sum := List.sum_map_mul_left _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (leaf_potential_bound r o₁ o₂ q hq B slots hnodup node hBR hfree hsize
        hbalance W hWslots hsplit) hC.le

/-- INTERNAL: Evaluate the two-hole root potential in its positive
completion totals and its two multipliers.
TEXLINE: main.tex:652-665 -/
theorem two_hole_potential {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n) (hpd : p ≠ d) (W : PairedGround n → ℝ) :
    nodePotential r o₁ o₂ q B U W (twoHoleRoot r o₁ o₂ q B U p d) =
      1 / (slotTotal r o₁ o₂ q B {p, d} U p * W p) +
        1 / (slotTotal r o₁ o₂ q B {p, d} U d * W d) := by
  classical
  let s := slotTotal r o₁ o₂ q B ({p, d} : PairedSet n) U
  have hp : 0 < s p := slot_total_pos r o₁ o₂ q hq B _ _ _
  have hd : 0 < s d := slot_total_pos r o₁ o₂ q hq B _ _ _
  change (∑ i ∈ ({p, d} : PairedSet n), s i *
    (if i = p then 1 / s p else if i = d then -1 / s d else 0) ^ 2 / W i) = _
  rw [Finset.sum_insert (by simpa using hpd), Finset.sum_singleton]
  simp only [ite_true, if_neg (Ne.symm hpd)]
  change s p * (1 / s p) ^ 2 / W p + s d * (-1 / s d) ^ 2 / W d = _
  have he (x z : ℝ) (hx : 0 < x) : x * (1 / x) ^ 2 / z = 1 / (x * z) := by
    field_simp
  rw [show (-1 / s d) ^ 2 = (1 / s d) ^ 2 by ring,
    he (s p) (W p) hp, he (s d) (W d) hd]

/-- INTERNAL: Evaluate the root future quadratic; its two off-diagonal
entries coincide and its diagonal entries vanish.
TEXLINE: main.tex:580-582,652-656 -/
theorem two_hole_future {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B : PairedSet n) (U : Finset (Fin n))
    (p d : PairedGround n) (hpd : p ≠ d) (t : Fin n) :
    nodeFuture r o₁ o₂ q B U (twoHoleRoot r o₁ o₂ q B U p d) t =
      -(2 * futureMatrix r o₁ o₂ q B {p, d} U t p d /
        (slotTotal r o₁ o₂ q B {p, d} U p * slotTotal r o₁ o₂ q B {p, d} U d)) := by
  classical
  let R : PairedSet n := {p, d}
  let s := slotTotal r o₁ o₂ q B R U
  let V := futureMatrix r o₁ o₂ q B R U t
  have hpp : V p p = 0 := by simp [V, futureMatrix]
  have hdd : V d d = 0 := by simp [V, futureMatrix]
  have hsym : V d p = V p d :=
    DefectSlotConservation.future_matrix_symmetric r o₁ o₂ q B R U t d p
  change (∑ i ∈ ({p, d} : PairedSet n), ∑ j ∈ ({p, d} : PairedSet n), V i j *
      (if i = p then 1 / s p else if i = d then -1 / s d else 0) *
      (if j = p then 1 / s p else if j = d then -1 / s d else 0)) = _
  simp only [Finset.sum_insert (show p ∉ ({d} : PairedSet n) by simpa using hpd), Finset.sum_singleton,
    ite_true, if_neg (Ne.symm hpd), hpp, hdd, hsym, zero_mul, zero_add, add_zero]
  change V p d * (1 / s p) * (-1 / s d) + V p d * (-1 / s d) * (1 / s p) =
    -(2 * V p d / (s p * s d))
  ring

end CountingMatroid.Analysis.SlotTransportFlow
