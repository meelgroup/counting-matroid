import CountingMatroid.Analysis.BalancedCliqueFlow
import CountingMatroid.Analysis.EmbeddedFlow
import CountingMatroid.Analysis.SlotDemandPairing

set_option autoImplicit false

/-!
Realize a terminal balanced demand node on its actual finite-set vertices.
The only conductance input is the lower bound on exchanges between those
vertices. This lemma does not assume disjointness of different leaves.
-/

namespace CountingMatroid.Analysis.LeafCliqueFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing

/-- PAPER: main.tex:670-674
The vertex obtained by omitting one displayed hole at a terminal node. -/
def leafVertex {n : ℕ} (B R : PairedSet n) (hole : R) : PairedSet n :=
  B ∪ R.erase hole.val

/-- INTERNAL: Distinct holes give distinct leaf vertices because each
omitted label is absent from the fixed base.
TEXLINE: main.tex:670-674 -/
theorem leaf_vertex_injective {n : ℕ} (B R : PairedSet n)
    (hBR : Disjoint B R) : Function.Injective (leafVertex B R) := by
  classical
  intro x y hxy
  apply Subtype.ext
  by_contra hne
  have hxB : x.val ∉ B := fun hx => Finset.disjoint_left.mp hBR hx x.property
  have hxin : x.val ∈ leafVertex B R y :=
    Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne, x.property⟩)
  have hxout : x.val ∉ leafVertex B R x := by
    simp [leafVertex, hxB]
  exact hxout (hxy.symm ▸ hxin)

/-- INTERNAL: The union of two distinct clique vertices recovers the
entire selected leaf set, so an exchange edge determines that set.
TEXLINE: main.tex:681-683 -/
theorem leaf_vertex_union {n : ℕ} (B R : PairedSet n) (x y : R) (hxy : x ≠ y) :
    leafVertex B R x ∪ leafVertex B R y = B ∪ R := by
  classical
  have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  ext z
  simp only [leafVertex, Finset.mem_union, Finset.mem_erase]
  by_cases hz : z = x.val
  · subst z
    simp [hne, x.property]
  · tauto

/-- PAPER: main.tex:670-683
A terminal balanced node has a supported flow on its actual state vertices.
A lower bound by the minimum vertex capacity gives the leaf potential
bound, with an arbitrary positive common scaling factor. -/
theorem leaf_clique_flow {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B : PairedSet n) (node : DemandNode n)
    (hBR : Disjoint B node.holes) (hne : node.holes.Nonempty)
    (hbalance : Balanced r o₁ o₂ q B ∅ node)
    (W : PairedGround n → ℝ) (hW : ∀ i ∈ node.holes, 0 < W i)
    (κ : PairedSet n → PairedSet n → ℝ) (C : ℝ) (hC : 0 < C)
    (hsym : ∀ s t, κ s t = κ t s)
    (hcap : ∀ x y : node.holes, x ≠ y →
      min (W x * slotTotal r o₁ o₂ q B node.holes ∅ x)
        (W y * slotTotal r o₁ o₂ q B node.holes ∅ y) ≤
          C * κ (leafVertex B node.holes x) (leafVertex B node.holes y)) :
    ∃ flow : FlowCertificate κ (fun state => ∑ hole : node.holes,
        if leafVertex B node.holes hole = state then
          slotTotal r o₁ o₂ q B node.holes ∅ hole * node.values hole else 0),
      flowEnergy κ flow.current ≤ C * nodePotential r o₁ o₂ q B ∅ W node ∧
      (∀ s t, flow.current s t ≠ 0 → s ∪ t = B ∪ node.holes) := by
  classical
  letI : Nonempty node.holes := ⟨⟨hne.choose, hne.choose_spec⟩⟩
  let v := leafVertex B node.holes
  let f := fun i : node.holes => slotTotal r o₁ o₂ q B node.holes ∅ i
  let c := fun i : node.holes => W i * f i
  let g := fun i : node.holes => f i * node.values i
  have hf : ∀ i, 0 < f i := fun i => slot_total_pos r o₁ o₂ q hq B _ _ i
  have hc : ∀ i, 0 < c i := fun i => mul_pos (hW i i.property) (hf i)
  have hbal : ∑ i, g i = 0 := by
    dsimp only [g, f]
    rw [Finset.sum_coe_sort node.holes (fun i =>
      slotTotal r o₁ o₂ q B node.holes ∅ i * node.values i)]
    exact hbalance
  obtain ⟨hub, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset node.holes) c
    Finset.univ_nonempty
  obtain ⟨localFlow, _, hlocalCost⟩ := BalancedCliqueFlow.star_flow
    (fun x y => κ (v x) (v y)) (fun i => c i / C) g hub hbal
    (fun i => hsym _ _) (fun i => div_pos (hc i) hC) (by
      intro i hi
      apply (div_le_iff₀ hC).mpr
      have hh := hcap i hub hi
      rw [min_eq_left (hmax i (Finset.mem_univ i))] at hh
      simpa only [mul_comm] using hh)
  have hv : Function.Injective v := leaf_vertex_injective B node.holes hBR
  obtain ⟨flow, hcurrent, henergy⟩ := EmbeddedFlow.embed_flow v hv κ g localFlow
  refine ⟨flow, henergy.trans_le (hlocalCost.trans ?_), ?_⟩
  · have hcost : (∑ i, (g i) ^ 2 / (c i / C)) =
        C * nodePotential r o₁ o₂ q B ∅ W node := by
      dsimp only [nodePotential, g, c, f]
      rw [Finset.sum_coe_sort node.holes (fun i =>
        (slotTotal r o₁ o₂ q B node.holes ∅ i * node.values i) ^ 2 /
          (W i * slotTotal r o₁ o₂ q B node.holes ∅ i / C)), Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      have hfi := slot_total_pos r o₁ o₂ q hq B node.holes ∅ i
      field_simp [hfi.ne', (hW i hi).ne', hC.ne']
      <;> ring
    exact le_of_eq hcost
  · intro s t hnonzero
    rw [hcurrent] at hnonzero
    have hs : ∃ x, v x = s := by
      by_contra hx
      have hz := EmbeddedFlow.embedded_current_off_image v localFlow.current s t
        (Or.inl (by simpa using hx))
      exact hnonzero hz
    have ht : ∃ y, v y = t := by
      by_contra hy
      have hz := EmbeddedFlow.embedded_current_off_image v localFlow.current s t
        (Or.inr (by simpa using hy))
      exact hnonzero hz
    obtain ⟨x, rfl⟩ := hs
    obtain ⟨y, rfl⟩ := ht
    have hxy : x ≠ y := by
      rintro rfl
      have ha := localFlow.antisymmetric x x
      have hz : localFlow.current x x = 0 := by linarith
      exact hnonzero ((EmbeddedFlow.embedded_current_apply v hv localFlow.current x x).trans hz)
    exact leaf_vertex_union B node.holes x y hxy

end CountingMatroid.Analysis.LeafCliqueFlow
