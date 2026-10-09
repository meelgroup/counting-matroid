import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.DefectTransportTwoPairs
import CountingMatroid.Analysis.OmittedRankWeightPolynomial
import CountingMatroid.Analysis.DefectSlotSplitSignature
import CountingMatroid.Analysis.DefectSlotConservation
import CountingMatroid.Analysis.SlotDemandRecursion
import CountingMatroid.Analysis.SlotTransportFlow
import CountingMatroid.Analysis.DefectSlotRoot
import CountingMatroid.Analysis.LeafExchangeProposal
import CountingMatroid.Analysis.DefectSlotBudget
import CountingMatroid.Analysis.DefectLeafClassifier

set_option autoImplicit false

/-!
The defect/event transport bound before applying goodness or the three-pair
coefficient inequality. The n = 2 branch uses its actual one-edge current.
For n ≥ 3, the balanced demand tree is realized by the leaf stars in
SlotTransportFlow. Shared-state demands cancel by first-moment conservation,
and distinct leaves use disjoint edges, so their flow energies add.
DefectSlotRoot identifies the exact source and event demands; DefectLeafClassifier
and LeafExchangeProposal identify the operational vertex and edge capacities;
DefectSlotFutureBound and DefectSlotBudget give the final partition-sum bound.
The all-node quadratic signature input is supplied by
DefectSlotSplitSignature.slot_split_control, whose proof obligations live there.
-/
namespace CountingMatroid.Analysis.DefectTransportRaw

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: The two new holes balance their children, have opposite
values, and contribute exactly the quadratic split cost.
TEXLINE: main.tex:531-567 -/
private theorem balanced_hole_split {α : Type*} [DecidableEq α]
    (R : Finset α) (sₐ sᵦ h : α → ℝ) (u : ℝ) (hu : 0 < u)
    (hbalance : ∑ i ∈ R, (sₐ i + sᵦ i) * h i = 0) :
    let X := ∑ i ∈ R, sₐ i * h i
    let Y := ∑ i ∈ R, sᵦ i * h i
    let hₐ := -X / u
    let hᵦ := -Y / u
    X + u * hₐ = 0 ∧ Y + u * hᵦ = 0 ∧ hₐ + hᵦ = 0 ∧
      u * hₐ ^ 2 + u * hᵦ ^ 2 = 2 * X ^ 2 / u := by
  intro X Y hₐ hᵦ
  have hXY : X + Y = 0 := by
    dsimp only [X, Y]
    simpa only [add_mul, Finset.sum_add_distrib] using hbalance
  have hY : Y = -X := by linarith
  have hsum : hₐ + hᵦ = 0 := by
    dsimp only [hₐ, hᵦ]
    rw [← add_div, ← neg_add, hXY]
    simp
  refine ⟨?_, ?_, hsum, ?_⟩
  · dsimp only [hₐ]
    rw [mul_div_cancel₀ _ hu.ne']
    ring
  · dsimp only [hᵦ]
    rw [mul_div_cancel₀ _ hu.ne']
    ring
  · dsimp only [hₐ, hᵦ]
    rw [hY]
    field_simp
    ring

/-- INTERNAL: Specialize the paper's slot transport to the defect/event
slots and bound the off-subgraph totals by full defect partition sums.
No goodness or defect-coefficient inequality is used in this bound.
TEXLINE: main.tex:493-709,868-898 -/
theorem defect_transport_raw (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤ (2 * (n : ℝ) ^ 2) *
        (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
          (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
            ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
              (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
  classical
  intro π κ D
  by_cases hn2 : n = 2
  · subst n
    obtain ⟨flow, hflow⟩ := DefectTransportTwoPairs.defect_transport_two_pairs
      r o₁ o₂ q w hn hq hw i k hik a b hA
    refine ⟨flow, hflow.trans ?_⟩
    have hslots : ∀ t : Fin 2, ¬ (t ≠ i ∧ t ≠ k) := by
      intro t h
      have hi : i.val ≠ k.val := fun he => hik (Fin.ext he)
      have hti : t.val ≠ i.val := fun he => h.1 (Fin.ext he)
      have htk : t.val ≠ k.val := fun he => h.2 (Fin.ext he)
      omega
    have hsum : (∑ t : Fin 2, if h : t ≠ i ∧ t ≠ k then
        (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [dif_neg (hslots t)]
    rw [hsum]
    norm_num [π]
  ·
    have hn3 : 3 ≤ n := by
      have hi : i.val ≠ k.val := fun he => hik (Fin.ext he)
      omega
    let A := pairEvent i k a b
    obtain ⟨hZ, _, _, hdef⟩ :=
      StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
    have hDcoeff : D ⟨i, k, hik⟩ =
        ∑ state : PairedSet n,
          if ConditionalDefectCoefficients.Respects (fun _ => none) state ∧
              (classifyState state).val = .defect i k then
            MvPolynomial.coeff (OmittedRankWeightPolynomial.omittedExponent state)
              (OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q)
          else 0 := by
      rw [OmittedRankWeightPolynomial.defect_coefficient_sum
        r o₁ o₂ q (fun _ => none) ⟨i, k, hik⟩,
        ConditionalDefectCoefficients.defect_total_empty]
    have hDpos : 0 < D ⟨i, k, hik⟩ := by
      rw [hDcoeff]
      exact OmittedRankWeightPolynomial.defect_coefficient_total_pos
        r o₁ o₂ q hq (fun _ => none) ⟨i, k, hik⟩ rfl rfl
    have hd : 0 < classMass π (.defect i k) := by
      dsimp only [π]
      rw [operational_class_mass, hdef ⟨i, k, hik⟩]
      exact_mod_cast div_pos (mul_pos (hw _) hDpos) hZ
    let source := fun state : PairedSet n =>
      if (classifyState state).val = .defect i k then
        π state / classMass π (.defect i k) else 0
    let sink := fun state : PairedSet n =>
      if state ∈ A then π state / eventMass π A else 0
    have hsource : (∑ state, source state) = 1 := by
      have heq : (∑ state, source state) =
          classMass π (.defect i k) / classMass π (.defect i k) := by
        change _ = (∑ state, if (classifyState state).val = .defect i k then π state else 0) / _
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro state _
        dsimp only [source]
        split_ifs <;> simp
      exact heq.trans (div_self hd.ne')
    have hsink : (∑ state, sink state) = 1 := by
      calc
        _ = ∑ state ∈ A, π state / eventMass π A := by
          dsimp only [sink]
          rw [← Finset.sum_filter]
          simp
        _ = eventMass π A / eventMass π A := by rw [← Finset.sum_div]; rfl
        _ = 1 := div_self hA.ne'
    let J := fun state next : PairedSet n =>
      source state * sink next - source next * sink state
    have hanti : ∀ state next, J state next = -J next state := by
      intro state next
      dsimp only [J]
      ring
    have hdiv : ∀ state,
        divergence J state = conditionalMeanDemand π (.defect i k) A state := by
      intro state
      simp only [divergence, J, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hsource, hsink, mul_one, one_mul]
      rfl
    suffices hassembly :
        DefectSlotSplitSignature.SlotSplitControl n r o₁ o₂ q →
        DefectSlotConservation.SlotConservationControl n r o₁ o₂ q →
        SlotDemandRecursion.DemandRecursionControl n r o₁ o₂ q →
          ∃ flow : FlowCertificate κ
              (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
            flowEnergy κ flow.current ≤ (2 * (n : ℝ) ^ 2) *
              (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
                (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                  ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                    (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      have hsplit := DefectSlotSplitSignature.slot_split_control n r M₁ M₂ o₁ o₂ q
        hfull hr h₁ h₂ hq hqone
      exact hassembly hsplit
        (DefectSlotConservation.slot_conservation_control n r o₁ o₂ q)
        (SlotDemandRecursion.demand_recursion_control n r o₁ o₂ q hq hsplit)
    intro hsplitControl hconservation hrecursion
    -- INTERNAL: Realize the paper's new-hole values at every admissible
    -- node and bound their cost using the supplied all-node split control.
    have controlledSplit (B R : PairedSet n) (U : Finset (Fin n))
        (hBR : Disjoint B R)
        (hU : ∀ t ∈ U, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
        (hsize : B.card + R.card + U.card = n + 1)
        (t : Fin n) (ht : t ∈ U) (h : PairedGround n → ℝ) :
        let sₐ := fun hole => DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, false) R) (U.erase t) hole
        let sᵦ := fun hole => DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, true) R) (U.erase t) hole
        let u := DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, false) R) (U.erase t) (t, false)
        (∑ hole ∈ R, DefectSlotSplitSignature.slotTotal r o₁ o₂ q B R U hole * h hole) = 0 →
        ∃ hₐ hᵦ : ℝ,
          (∑ hole ∈ R, sₐ hole * h hole) + u * hₐ = 0 ∧
          (∑ hole ∈ R, sᵦ hole * h hole) + u * hᵦ = 0 ∧
          hₐ + hᵦ = 0 ∧
          u * hₐ ^ 2 + u * hᵦ ^ 2 ≤
            -(∑ hole ∈ R, ∑ other ∈ R,
              DefectSlotSplitSignature.futureMatrix r o₁ o₂ q B R U t hole other *
                h hole * h other) := by
      intro sₐ sᵦ u hbalance
      have hchildBalance : (∑ hole ∈ R, (sₐ hole + sᵦ hole) * h hole) = 0 := by
        calc
          _ = ∑ hole ∈ R, DefectSlotSplitSignature.slotTotal r o₁ o₂ q B R U hole *
              h hole := by
            apply Finset.sum_congr rfl
            intro hole hhole
            rw [hconservation.old_hole B R U t ht (hU t ht) hole hhole]
          _ = 0 := hbalance
      have hu : 0 < u := DefectSlotSplitSignature.slot_total_pos r o₁ o₂ q hq B _ _ _
      obtain ⟨hbalₐ, hbalᵦ, hopp, hcost⟩ := balanced_hole_split R sₐ sᵦ h u hu hchildBalance
      refine ⟨-(∑ hole ∈ R, sₐ hole * h hole) / u,
        -(∑ hole ∈ R, sᵦ hole * h hole) / u, hbalₐ, hbalᵦ, hopp, ?_⟩
      rw [hcost]
      exact hsplitControl B R U hBR hU hsize t ht h hchildBalance
    -- Instantiate the proved demand recursion at the paper's defect/event
    -- slots: B={a_k}, p=a_i, d=b_k, with every other original pair ordinary.
    let p : PairedGround n := (i, !a)
    let d : PairedGround n := (k, b)
    let B : PairedSet n := {(k, !b)}
    let U : Finset (Fin n) := (Finset.univ.erase i).erase k
    let root := SlotDemandRecursion.twoHoleRoot r o₁ o₂ q B U p d
    have hpd : p ≠ d := fun he => hik (congrArg Prod.fst he)
    have hrootBalance : SlotDemandRecursion.Balanced r o₁ o₂ q B U root :=
      hrecursion.root_balanced B U p d hpd
    have hrootHoles : root.holes = {p, d} := rfl
    have hBR : Disjoint B root.holes := by
      rw [hrootHoles, Finset.disjoint_left]
      intro e he hf
      have heq : e = (k, !b) := Finset.mem_singleton.mp he
      subst e
      rcases Finset.mem_insert.mp hf with hp | hd
      · exact hik ((congrArg Prod.fst hp).symm)
      · have hmate : (!b) = b := congrArg Prod.snd (Finset.mem_singleton.mp hd)
        exact Bool.not_ne_self b hmate
    have hfree : ∀ t ∈ U, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ root.holes := by
      intro t ht c
      obtain ⟨htk, hti, _⟩ := Finset.mem_erase.mp ht |>.imp_right Finset.mem_erase.mp
      constructor
      · intro hm
        exact htk (congrArg Prod.fst (Finset.mem_singleton.mp hm))
      · rw [hrootHoles]
        intro hm
        rcases Finset.mem_insert.mp hm with hp | hd
        · exact hti (congrArg Prod.fst hp)
        · exact htk (congrArg Prod.fst (Finset.mem_singleton.mp hd))
    have hcardU : U.card = n - 2 := by
      dsimp only [U]
      rw [Finset.card_erase_of_mem (by simp [Ne.symm hik]),
        Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have hsize : B.card + root.holes.card + U.card = n + 1 := by
      rw [hrootHoles, Finset.card_insert_of_notMem (by simpa using hpd),
        Finset.card_singleton, hcardU]
      have hBcard : B.card = 1 := Finset.card_singleton _
      simp only [Finset.card_singleton]
      omega
    let W : PairedGround n → ℝ := fun hole =>
      if hole.1 = i then (w ⟨i, k, hik⟩ : ℝ)
      else if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
    have hW : ∀ t ∈ U.toList,
        W (t, false) = W (t, true) ∧ 0 < W (t, false) := by
      intro t _
      refine ⟨rfl, ?_⟩
      dsimp only [W]
      split_ifs
      · exact_mod_cast hw ⟨i, k, hik⟩
      · exact zero_lt_one
      · exact_mod_cast hw _
    obtain ⟨leaves, hnonempty, hleafBalance, hrootKeep, hleafPotential⟩ :=
      hrecursion.tree B U.toList U.nodup_toList root hBR
        (fun t ht c => hfree t (Finset.mem_toList.mp ht) c)
        (by simpa only [Finset.toList_toFinset] using hsize)
        (by simpa only [Finset.toList_toFinset] using hrootBalance) W hW
    let C : ℝ := (2 * (n : ℝ) ^ 2) * (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
    have hC : 0 < C := by
      have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
      have hZreal : (0 : ℝ) < (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) := by exact_mod_cast hZ
      exact mul_pos (mul_pos (by norm_num) (pow_pos hnreal _)) hZreal
    have hWall : ∀ hole, 0 < W hole := by
      intro hole
      dsimp only [W]
      split_ifs
      · exact_mod_cast hw ⟨i, k, hik⟩
      · exact zero_lt_one
      · exact_mod_cast hw _
    have hκsym : ∀ state next, κ state next = κ next state := by
      intro state next
      dsimp only [κ]
      rw [exchange_proposal_symmetric, min_comm]
    suffices hoperational :
        SlotTransportFlow.completionDemand r o₁ o₂ q B U root =
          conditionalMeanDemand π (.defect i k) (pairEvent i k a b) ∧
        (∀ leaf ∈ SlotDemandRecursion.leafNodes r o₁ o₂ q B U.toList root,
          ∀ x y : leaf.holes, x ≠ y →
            min (W x * DefectSlotSplitSignature.slotTotal r o₁ o₂ q B leaf.holes ∅ x)
              (W y * DefectSlotSplitSignature.slotTotal r o₁ o₂ q B leaf.holes ∅ y) ≤
                C * κ (LeafCliqueFlow.leafVertex B leaf.holes x)
                  (LeafCliqueFlow.leafVertex B leaf.holes y)) ∧
        C * (SlotDemandRecursion.nodePotential r o₁ o₂ q B U W root -
          ∑ t ∈ U, SlotDemandRecursion.nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
          (2 * (n : ℝ) ^ 2) *
            (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
              (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                  (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      obtain ⟨hdemand, hcapacity, hbudget⟩ := hoperational
      obtain ⟨flow, hflow⟩ := SlotTransportFlow.slot_transport_flow r o₁ o₂ q hq B
        U.toList U.nodup_toList root ⟨p, by rw [hrootHoles]; simp⟩ hBR
        (fun t ht c => hfree t (Finset.mem_toList.mp ht) c)
        (by simpa only [Finset.toList_toFinset] using hsize)
        (by simpa only [Finset.toList_toFinset] using hrootBalance) W hW hsplitControl
        κ C hC hκsym (fun leaf _ hole _ => hWall hole) hcapacity
      let adjusted : FlowCertificate κ
          (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)) :=
        { current := flow.current
          antisymmetric := flow.antisymmetric
          supported := flow.supported
          divergence_eq := fun state => (flow.divergence_eq state).trans (by
            simpa only [Finset.toList_toFinset] using congrFun hdemand state) }
      refine ⟨adjusted, hflow.trans ?_⟩
      simpa only [Finset.toList_toFinset] using hbudget
    refine ⟨DefectSlotRoot.root_demand_eq r o₁ o₂ q w hq hw i k hik a b hA, ?_⟩
    suffices hremaining :
        (∀ leaf ∈ SlotDemandRecursion.leafNodes r o₁ o₂ q B U.toList root,
          ∀ hole : leaf.holes,
            W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q B leaf.holes ∅ hole =
              (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
                π (LeafCliqueFlow.leafVertex B leaf.holes hole)) ∧
        C * (SlotDemandRecursion.nodePotential r o₁ o₂ q B U W root -
          ∑ t ∈ U, SlotDemandRecursion.nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
          (2 * (n : ℝ) ^ 2) *
            (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
              (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                  (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      refine ⟨?_, hremaining.2⟩
      intro leaf hl x y hxy
      have hleafBR := SlotLeafGeometry.leaf_holes_disjoint r o₁ o₂ q B U.toList root hBR
        (fun t ht c => (hfree t (Finset.mem_toList.mp ht) c).1) leaf hl
      exact LeafExchangeProposal.scaled_leaf_conductance_lower n hn B leaf.holes hleafBR
        π π.p_nonneg (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
        (by exact_mod_cast hZ) _ (hremaining.1 leaf hl) x y hxy
    refine ⟨?_, DefectSlotBudget.defect_slot_budget r o₁ o₂ q w hq hw i k hik a b hA⟩
    intro leaf hl hole
    obtain ⟨choices, hshape⟩ := SlotLeafGeometry.leaf_holes_shape r o₁ o₂ q B U.toList
      U.nodup_toList root leaf hl
    simp only [Finset.toList_toFinset] at hshape
    exact DefectLeafClassifier.defect_leaf_operational_weight r o₁ o₂ q w hq hw
      i k hik a b leaf.holes choices hshape hole

end CountingMatroid.Analysis.DefectTransportRaw


/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the general branch through certified leaf stars, injective embedding, disjoint-edge flow summation, conserved root demand, operational leaf classification and proposal capacities, and the normalized root budget. All new helper obligations are proved; the imported all-node signature prerequisite remains with its separate owner.
* 2026-10-09 · partial · defined the operational omitted-element polynomial and proved its squarefree coefficient recovery, multiaffinity, and defect-total bridge; proved the numerical orthogonal-complement split bound, slot-completion coefficient bridge, and balanced new-hole equations with their exact cost. The parent now consumes the all-node SlotSplitControl invariant; its signature proof and recursive conservation/leaf-flow assembly remain open.
* 2026-10-09 · partial · proved and used the n = 2 no-ordinary-slot transport via the actual singleton defect/event states and a supported unit-edge current; the surviving branch has n ≥ 3. Located the recursive construction at main.tex:493-709 and its specialization at 868-898. The first split still needs the omitted-rank-weight Hessian signature, absent from the project and pinned libraries; positivity and balanced demands alone do not supply it.
-/
