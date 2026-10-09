import CountingMatroid.Analysis.ConditionalDefectCoefficients
import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.OnePairObservablePoincare
import CountingMatroid.Analysis.BalancedCliqueEnergy
import CountingMatroid.Analysis.ConditionalTransversalSlots
import CountingMatroid.Analysis.SlotTransportFlow
import CountingMatroid.Analysis.LeafExchangeProposal
import CountingMatroid.Analysis.ConditionalLeafClassifier

set_option autoImplicit false

/-!
The slot-transport specialization for a conditioning-tree split. Its
finite conditional means and restricted energy are defined here. Clearing
the two positive child totals reduces the node estimate to the paper's
singleton-slot transport inequality. The one-pair branch is proved using
the balanced leaf-clique estimate. The general branch now specializes the
proved balanced-demand recursion and disjoint leaf-flow assembly, with exact
root coefficients and assignment-respecting energy. Its remaining obligation
is the operational classifier on the terminal leaf vertices, isolated in
ConditionalLeafClassifier; its general forward transversal-classifier bridge
is currently downstream.
-/

namespace CountingMatroid.Analysis.ConditionalTransversalSplitTransport

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- PAPER: main.tex:815-817
Conditional transversal mean at an assignment, using operational weights. -/
noncomputable def conditionalMean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (H : PairedSet n → ℝ) : ℝ := by
  classical
  exact (∑ A : Finset (Fin n), if SubsetRespects σ A then
    (q ^ transversalDeficiency r o₁ o₂ A : ℚ) * H (transversalState A) else 0) /
      (transversalTotal r o₁ o₂ q σ : ℝ)

/-- INTERNAL: The unnormalized centered moment at one conditioning node.
TEXLINE: main.tex:832-839 -/
noncomputable def conditionalMoment {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (H : PairedSet n → ℝ) : ℝ := by
  classical
  exact ∑ A : Finset (Fin n), if SubsetRespects σ A then
    (q ^ transversalDeficiency r o₁ o₂ A : ℚ) *
      (H (transversalState A) - conditionalMean r o₁ o₂ q σ H) ^ 2 else 0

/-- PAPER: main.tex:822-824
The energy over endpoints both respecting a conditioning assignment. The
factor converting this normalized energy to D_sigma is kept in the bound. -/
noncomputable def nodeEnergy {n : ℕ} (κ : PairedSet n → PairedSet n → ℝ)
    (H : PairedSet n → ℝ) (σ : Assignment n) : ℝ := by
  classical
  exact (1 / 2 : ℝ) * ∑ state, ∑ next,
    if Respects σ state ∧ Respects σ next then
      κ state next * (H state - H next) ^ 2 else 0

/-- INTERNAL: Pair the assembled pointwise completion demand with a
potential by summing the same completion moments.
TEXLINE: main.tex:499-507,684-692 -/
theorem completion_demand_pairing {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (B : PairedSet n)
    (U : Finset (Fin n)) (node : SlotDemandRecursion.DemandNode n)
    (H : PairedSet n → ℝ) :
    (∑ state, SlotTransportFlow.completionDemand r o₁ o₂ q B U node state * H state) =
      SlotDemandPairing.nodePairing B U node (fun state =>
        ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ) *
          H state) := by
  classical
  unfold SlotTransportFlow.completionDemand SlotDemandPairing.nodePairing
    SlotDemandPairing.completionMoment
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro hole _
  simp only [mul_assoc, Finset.mul_sum, Finset.sum_mul, mul_ite, ite_mul,
    mul_zero, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const_zero]

/-- INTERNAL: The two-hole root pairing is the difference of the
conditional transversal means, with the missing singleton selecting its mate.
TEXLINE: main.tex:810-817 -/
theorem root_conditional_pairing {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (k : Fin n) (hk : σ k = none) (H : PairedSet n → ℝ) :
    let B := ConditionalTransversalSlots.fixedLabels σ
    let U := ConditionalTransversalSlots.ordinarySlots σ k
    let root := SlotDemandRecursion.twoHoleRoot r o₁ o₂ q B U (k, false) (k, true)
    SlotDemandPairing.nodePairing B U root (fun state =>
      ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ) * H state) =
      conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H := by
  classical
  intro B U root
  unfold SlotDemandPairing.nodePairing
  dsimp only [root, SlotDemandRecursion.twoHoleRoot]
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  simp only [ite_true, Prod.mk.injEq, Bool.true_eq_false, and_false, if_false]
  dsimp only [SlotDemandPairing.completionMoment, B, U]
  have hm₁ := ConditionalTransversalSlots.root_completion_sum σ k hk true
    (fun state => ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ) * H state)
  have hm₀ := ConditionalTransversalSlots.root_completion_sum σ k hk false
    (fun state => ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ) * H state)
  have ht₁ := ConditionalTransversalSlots.root_transversal_total r o₁ o₂ q σ k hk true
  have ht₀ := ConditionalTransversalSlots.root_transversal_total r o₁ o₂ q σ k hk false
  simp only [Bool.not_true, Bool.not_false] at hm₁ hm₀ ht₁ ht₀
  rw [hm₁, hm₀, ht₁, ht₀]
  unfold conditionalMean
  dsimp only [transversalDeficiency]
  ring

/-- PAPER: main.tex:455-709,815-829
Specialize slot transport to the two elements of the branching pair. Every
ordinary hole t then has multiplier w_(t,k), and v_t is c^sigma_(k,t).
This estimate precedes goodness and coefficient-score sink selection. -/
theorem conditional_transversal_split_transport (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (σ : Assignment n) (k : Fin n) (hk : σ k = none) (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    let z : ℝ := transversalTotal r o₁ o₂ q σ
    let s₀ : ℝ := transversalTotal r o₁ o₂ q (Function.update σ k (some false))
    let s₁ : ℝ := transversalTotal r o₁ o₂ q (Function.update σ k (some true))
    let V : ℝ := ∑ t : Fin n, if h : σ t = none ∧ t ≠ k then
      (defectTotal r o₁ o₂ q σ ⟨k, t, h.2.symm⟩ : ℝ) /
        (w ⟨t, k, h.2⟩ : ℝ) else 0
    (s₀ * s₁ / z) *
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
      (1 + 2 / z * V) *
        ((StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
          (2 * (n : ℝ) ^ 2) * nodeEnergy κ H σ) := by
  classical
  intro π κ z s₀ s₁ V
  have hz : 0 < z := by
    dsimp only [z]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq (Function.update σ k (some false))
  have hs₁ : 0 < s₁ := by
    dsimp only [s₁]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq (Function.update σ k (some true))
  have hsplit : s₀ + s₁ = z := by
    dsimp only [s₀, s₁, z]
    exact_mod_cast transversal_total_split r o₁ o₂ q σ k hk
  let B := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
    (2 * (n : ℝ) ^ 2) * nodeEnergy κ H σ
  suffices hraw :
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
          (1 / s₀ + 1 / s₁ + 2 / (s₀ * s₁) * V) * B by
    calc
      _ ≤ (s₀ * s₁ / z) * ((1 / s₀ + 1 / s₁ + 2 / (s₀ * s₁) * V) * B) :=
        mul_le_mul_of_nonneg_left hraw (div_nonneg (mul_pos hs₀ hs₁).le hz.le)
      _ = _ := by
        change _ = (1 + 2 / z * V) * B
        field_simp [hs₀.ne', hs₁.ne', hz.ne']
        rw [← hsplit]
        ring
  by_cases hn1 : n = 1
  · subst n
    have hk0 : k = 0 := Subsingleton.elim _ _
    subst k
    have hσ : σ = fun _ => none := by
      funext i
      have hi : i = 0 := Subsingleton.elim _ _
      simpa only [hi] using hk
    subst σ
    let x : PairedSet 1 := {(0, false)}
    let y : PairedSet 1 := {(0, true)}
    have hU : (Finset.univ : Finset (Finset (Fin 1))) = {∅, {0}} := by decide
    have htx : transversalState ({0} : Finset (Fin 1)) = x := by decide
    have hty : transversalState (∅ : Finset (Fin 1)) = y := by decide
    have hs₀weight : s₀ = (q ^ transversalDeficiency r o₁ o₂ {0} : ℚ) := by
      simp [s₀, transversalTotal, hU, SubsetRespects, Function.update]
    have hs₁weight : s₁ = (q ^ transversalDeficiency r o₁ o₂ ∅ : ℚ) := by
      simp [s₁, transversalTotal, hU, SubsetRespects, Function.update]
    have hm₀ : conditionalMean r o₁ o₂ q
        (Function.update (fun _ => none) 0 (some false)) H = H x := by
      have hp : (q : ℝ) ^ transversalDeficiency r o₁ o₂ {0} ≠ 0 := by
        exact_mod_cast (pow_pos hq (transversalDeficiency r o₁ o₂ {0})).ne'
      simp [conditionalMean, transversalTotal, hU, SubsetRespects,
        Function.update, hp, htx]
    have hm₁ : conditionalMean r o₁ o₂ q
        (Function.update (fun _ => none) 0 (some true)) H = H y := by
      have hp : (q : ℝ) ^ transversalDeficiency r o₁ o₂ ∅ ≠ 0 := by
        exact_mod_cast (pow_pos hq (transversalDeficiency r o₁ o₂ ∅)).ne'
      simp [conditionalMean, transversalTotal, hU, SubsetRespects,
        Function.update, hp, hty]
    let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
    have hZ : 0 < Z := by
      dsimp only [Z]
      exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
        r o₁ o₂ q 1 w hq hw).1
    have hclassx : (classifyState x).val = .transversal := by decide
    have hclassy : (classifyState y).val = .transversal := by decide
    have hπx : π x = s₀ / Z := by
      rw [hs₀weight]
      simp [π, Z, operationalLaw, StationaryMeanIdentities.stateWeight,
        hclassx, weightOfKind, CountingMatroid.Model.Operations.natSub,
        BoundedRunResourceEnvelope.ratPower_value, transversalDeficiency, htx]
    have hπy : π y = s₁ / Z := by
      rw [hs₁weight]
      simp [π, Z, operationalLaw, StationaryMeanIdentities.stateWeight,
        hclassy, weightOfKind, CountingMatroid.Model.Operations.natSub,
        BoundedRunResourceEnvelope.ratPower_value, transversalDeficiency, hty]
    have hπempty : π ∅ = 0 := by
      have hc : (classifyState (∅ : PairedSet 1)).val = .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hc, weightOfKind]
    have hπfull : π {(0, false), (0, true)} = 0 := by
      have hc : (classifyState ({(0, false), (0, true)} : PairedSet 1)).val =
          .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hc, weightOfKind]
    have hQxy : exchangeProposal 1 hn x y = (1 / 2 : ℝ) := by
      simp [exchangeProposal, exchangeState, x, y, Fintype.sum_prod_type,
        PairedGround]
      norm_num
    have hQyx : exchangeProposal 1 hn y x = (1 / 2 : ℝ) := by
      rw [exchange_proposal_symmetric]
      exact hQxy
    have hmin0 (state : PairedSet 1) : min 0 (π state) = 0 :=
      min_eq_left (π.coe_nonneg state)
    have hmin0' (state : PairedSet 1) : min (π state) 0 = 0 :=
      min_eq_right (π.coe_nonneg state)
    have henergy : nodeEnergy κ H (fun _ => none) =
        (1 / 2 : ℝ) * min (π x) (π y) * (H x - H y) ^ 2 := by
      simp only [nodeEnergy, Respects, reduceCtorEq, IsEmpty.forall_iff,
        implies_true, and_self, if_true, κ,
        OnePairObservablePoincare.one_pair_state_sum, hπempty, hπfull,
        hmin0, hmin0', mul_zero, zero_mul, sub_self, zero_pow (by decide : 2 ≠ 0),
        zero_add, add_zero]
      change (1 / 2 : ℝ) *
        (exchangeProposal 1 hn x y * min (π x) (π y) * (H x - H y) ^ 2 +
          exchangeProposal 1 hn y x * min (π y) (π x) * (H y - H x) ^ 2) = _
      rw [hQxy, hQyx, min_comm (π y) (π x)]
      ring
    have hV : V = 0 := by simp [V, Fin.sum_univ_one]
    let c := fun b : Bool => if b then s₁ else s₀
    let g := fun b : Bool => if b then (-1 : ℝ) else 1
    let F := fun b : Bool => if b then H y else H x
    have hc : ∀ b, 0 < c b := by intro b; cases b <;> assumption
    have hbalance : (∑ b, g b) = 0 := by simp [g]
    have hhub : ∃ hub : Bool, ∀ b, c b ≤ c hub := by
      rcases le_total s₀ s₁ with h | h
      · exact ⟨true, by intro b; cases b <;> simp [c, h]⟩
      · exact ⟨false, by intro b; cases b <;> simp [c, h]⟩
    obtain ⟨hub, hmax⟩ := hhub
    have hclique := BalancedCliqueEnergy.balanced_clique_pairing_sq_le
      c g F hc hbalance hub hmax
    have hpairing : (∑ b, g b * F b) = H x - H y := by
      simp [g, F]
      ring
    have hcost : (∑ b, (g b) ^ 2 / c b) = 1 / s₀ + 1 / s₁ := by
      simp [g, c, add_comm]
    have hcliqueEnergy : potentialEnergy (fun a b => min (c a) (c b)) F =
        min s₀ s₁ * (H x - H y) ^ 2 := by
      simp [potentialEnergy, c, F, min_comm]
      ring
    rw [hpairing, hcost, hcliqueEnergy] at hclique
    have hscaled : Z * min (s₀ / Z) (s₁ / Z) = min s₀ s₁ := by
      rw [mul_min_of_nonneg _ _ hZ.le, mul_div_cancel₀ _ hZ.ne',
        mul_div_cancel₀ _ hZ.ne']
    rw [hm₀, hm₁, hV]
    simp only [mul_zero, add_zero]
    dsimp only [B]
    rw [henergy, hπx, hπy]
    norm_num only [Nat.cast_one]
    change (H x - H y) ^ 2 ≤
      (1 / s₀ + 1 / s₁) * (Z * 2 *
        ((1 / 2 : ℝ) * min (s₀ / Z) (s₁ / Z) * (H x - H y) ^ 2))
    have heq : Z * 2 *
        ((1 / 2 : ℝ) * min (s₀ / Z) (s₁ / Z) * (H x - H y) ^ 2) =
          min s₀ s₁ * (H x - H y) ^ 2 := by
      calc
        _ = (Z * min (s₀ / Z) (s₁ / Z)) * (H x - H y) ^ 2 := by ring
        _ = _ := by rw [hscaled]
    rw [heq]
    exact hclique
  have hn2 : 2 ≤ n := by omega
  let base := ConditionalTransversalSlots.fixedLabels σ
  let U := ConditionalTransversalSlots.ordinarySlots σ k
  let root := SlotDemandRecursion.twoHoleRoot r o₁ o₂ q base U (k, false) (k, true)
  let W : PairedGround n → ℝ := fun hole =>
    if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  let C := Z * (2 * (n : ℝ) ^ 2)
  let restricted := fun state next : PairedSet n =>
    if Respects σ state ∧ Respects σ next then κ state next else 0
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
      r o₁ o₂ q 1 w hq hw).1
  have hC : 0 < C := by dsimp [C]; positivity
  have hrestricted : ∀ state next, 0 ≤ restricted state next := by
    intro state next
    dsimp only [restricted]
    split_ifs
    · exact mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
        (le_min (π.coe_nonneg state) (π.coe_nonneg next))
    · exact le_rfl
  have hsym : ∀ state next, restricted state next = restricted next state := by
    intro state next
    dsimp only [restricted, κ]
    simp only [and_comm, exchange_proposal_symmetric, min_comm]
  have hW : ∀ hole, 0 < W hole := by
    intro hole
    dsimp only [W]
    split_ifs
    · norm_num
    · exact_mod_cast hw _
  have hroot : root.holes = {(k, false), (k, true)} := rfl
  have hpd : (k, false) ≠ (k, true) := by simp
  obtain ⟨hBR, hfree, hsize⟩ := ConditionalTransversalSlots.root_admissible σ k hk
  change Disjoint base root.holes at hBR
  change (∀ t ∈ U, ∀ b : Bool, (t, b) ∉ base ∧ (t, b) ∉ root.holes) at hfree
  change base.card + root.holes.card + U.card = n + 1 at hsize
  have hbalance : SlotDemandRecursion.Balanced r o₁ o₂ q base U root :=
    SlotDemandRecursion.two_hole_root_balanced r o₁ o₂ q hq base U _ _ hpd
  have hWslots : ∀ t ∈ U.toList, W (t, false) = W (t, true) ∧ 0 < W (t, false) := by
    intro t _
    exact ⟨rfl, hW _⟩
  have hsp : DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, false) = s₁ := by
    simpa only [Bool.not_true, base, U, root, SlotDemandRecursion.twoHoleRoot, s₁] using
      ConditionalTransversalSlots.root_transversal_total r o₁ o₂ q σ k hk true
  have hsd : DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, true) = s₀ := by
    simpa only [Bool.not_false, base, U, root, SlotDemandRecursion.twoHoleRoot, s₀] using
      ConditionalTransversalSlots.root_transversal_total r o₁ o₂ q σ k hk false
  have hpotential : SlotDemandRecursion.nodePotential r o₁ o₂ q base U W root =
      1 / s₀ + 1 / s₁ := by
    rw [SlotTransportFlow.two_hole_potential r o₁ o₂ q hq base U _ _ hpd W]
    simp only [W, dif_pos rfl, mul_one]
    change 1 / DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, false) +
      1 / DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, true) = _
    rw [hsp, hsd, add_comm]
  have hfuture : (∑ t ∈ U,
      SlotDemandRecursion.nodeFuture r o₁ o₂ q base U root t / W (t, false)) =
      -(2 / (s₀ * s₁) * V) := by
    have hV : V = ∑ t ∈ U, if h : σ t = none ∧ t ≠ k then
        (defectTotal r o₁ o₂ q σ ⟨k, t, h.2.symm⟩ : ℝ) /
          (w ⟨t, k, h.2⟩ : ℝ) else 0 := by
      dsimp only [V, U, ConditionalTransversalSlots.ordinarySlots]
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro t _
      split_ifs <;> rfl
    rw [hV, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t ht
    have hguard := (ConditionalTransversalSlots.mem_ordinary_slots σ k t).mp ht
    rw [dif_pos hguard, SlotTransportFlow.two_hole_future r o₁ o₂ q base U _ _ hpd t]
    change -(2 * DefectSlotSplitSignature.futureMatrix r o₁ o₂ q base root.holes U t
      (k, false) (k, true) /
      (DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, false) *
        DefectSlotSplitSignature.slotTotal r o₁ o₂ q base root.holes U (k, true))) /
      W (t, false) = _
    rw [hsp, hsd]
    have hdef := ConditionalTransversalSlots.root_future_defect_total r o₁ o₂ q σ k hk t ht
    change DefectSlotSplitSignature.futureMatrix r o₁ o₂ q base root.holes U t
      (k, false) (k, true) = _ at hdef
    rw [hdef]
    simp only [W, dif_neg hguard.2]
    ring
  suffices hcap : ∀ leaf ∈ SlotDemandRecursion.leafNodes r o₁ o₂ q base U.toList root,
      ∀ x y : leaf.holes, x ≠ y →
        min (W x * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ x)
          (W y * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ y) ≤
            C * restricted (LeafCliqueFlow.leafVertex base leaf.holes x)
              (LeafCliqueFlow.leafVertex base leaf.holes y) by
    have hflow := SlotTransportFlow.slot_transport_flow r o₁ o₂ q hq base
      U.toList U.nodup_toList root (by rw [hroot]; simp) hBR
      (by simpa only [Finset.mem_toList] using hfree)
      (by simpa only [Finset.toList_toFinset] using hsize)
      (by simpa only [Finset.toList_toFinset] using hbalance) W hWslots
      (DefectSlotSplitSignature.slot_split_control n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone)
      restricted C hC hsym (fun leaf _ i _ => hW i) hcap
    simp only [Finset.toList_toFinset] at hflow
    obtain ⟨flow, hcost⟩ := hflow
    rw [hpotential, hfuture] at hcost
    have hpairing := flow.pairing_sq_le hrestricted
      (C * (1 / s₀ + 1 / s₁ + 2 / (s₀ * s₁) * V))
      (by simpa only [sub_neg_eq_add] using hcost) H
    simp only [Finset.toList_toFinset] at hpairing
    rw [completion_demand_pairing r o₁ o₂ q base U root H,
      root_conditional_pairing r o₁ o₂ q σ k hk H, sub_sq_comm] at hpairing
    have henergy : potentialEnergy restricted H = nodeEnergy κ H σ := by
      unfold potentialEnergy nodeEnergy restricted
      simp only [ite_mul, zero_mul]
    rw [henergy] at hpairing
    dsimp only [B, C, Z]
    exact hpairing.trans_eq (by ring)
  intro leaf hleaf x y hxy
  obtain ⟨choices, hshape⟩ := ConditionalTransversalSlots.leaf_holes_shape
    r o₁ o₂ q base U.toList U.nodup_toList root leaf hleaf
  simp only [Finset.toList_toFinset, hroot] at hshape
  have hleafBR : Disjoint base leaf.holes :=
    SlotLeafGeometry.leaf_holes_disjoint r o₁ o₂ q base U.toList root hBR
      (fun t ht c => (hfree t (Finset.mem_toList.mp ht) c).1) leaf hleaf
  have hrespect (hole : leaf.holes) :
      Respects σ (LeafCliqueFlow.leafVertex base leaf.holes hole) :=
    ConditionalTransversalSlots.conditional_leaf_respects σ k hk choices leaf.holes hshape hole
  have hvertex : ∀ hole : leaf.holes,
      W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole =
        Z * π (LeafCliqueFlow.leafVertex base leaf.holes hole) := by
    intro hole
    suffices hkind : (classifyState (LeafCliqueFlow.leafVertex base leaf.holes hole)).val =
        if hole.val.1 = k then .transversal else .defect hole.val.1 k by
      have hterminal : DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole =
          ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
            (LeafCliqueFlow.leafVertex base leaf.holes hole)).val) : ℚ) : ℝ) := by
        simp [DefectSlotSplitSignature.slotTotal, DefectSlotSplitSignature.SlotCompletion,
          LeafCliqueFlow.leafVertex]
      have hweight : (StationaryMeanIdentities.stateWeight r o₁ o₂ q w
          (LeafCliqueFlow.leafVertex base leaf.holes hole) : ℝ) =
          W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole := by
        rw [hterminal]
        by_cases hi : hole.val.1 = k
        · simp [StationaryMeanIdentities.stateWeight, hkind, hi, W, weightOfKind,
            CountingMatroid.Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value]
        · simp [StationaryMeanIdentities.stateWeight, hkind, hi, W, weightOfKind,
            CountingMatroid.Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value,
            CountingMatroid.Model.Operations.multiplierRead, CountingMatroid.Model.Operations.ratMul]
      rw [← hweight]
      change _ = Z * ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w
        (LeafCliqueFlow.leafVertex base leaf.holes hole) : ℝ) / Z)
      rw [mul_div_cancel₀ _ hZ.ne']
    exact ConditionalLeafClassifier.conditional_leaf_classifier σ k hk choices leaf.holes hshape hole
  have hscaled := LeafExchangeProposal.scaled_leaf_conductance_lower n hn
    base leaf.holes hleafBR π (fun state => π.coe_nonneg state) Z hZ
    (fun hole => W hole * DefectSlotSplitSignature.slotTotal r o₁ o₂ q base leaf.holes ∅ hole)
    hvertex x y hxy
  dsimp only [restricted]
  rw [if_pos ⟨hrespect x, hrespect y⟩]
  dsimp only [C, κ]
  exact hscaled.trans_eq (by ring)

end CountingMatroid.Analysis.ConditionalTransversalSplitTransport

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · handoff requested · parent body uses ConditionalLeafClassifier.conditional_leaf_classifier; its ordinary-hole defect case is proved and its branching-hole case reduces to the existing downstream forward classifier. The new child and the fully proved ConditionalTransversalSlots support are prepared for live scheduler capture; this reorganizes the remaining classifier proof debt and does not complete the theorem.
* 2026-10-09 · partial · assembled the general transport reduction using SlotTransportFlow and LeafExchangeProposal; proved and used root completion/total, doubled-slot defect coefficient, root admissibility, leaf-shape, assignment-respect, and completion-pairing bridges. The sole remaining local goal is terminal vertex classification (transversal at k, ordered defect otherwise); its general transversal bridge is downstream, while the upstream characterization is private. No open child lemma was introduced.
* 2026-10-09 · partial · proved the n = 1 branch through the separately proved balanced leaf-clique pairing bound; retained the exact theorem interface and positive-total coefficient cancellation. The n ≥ 2 branch needs the all-stage balanced-demand recursion, ordinary-hole cancellation, and disjoint leaf-edge charge. Verified the zero-proposal obstruction to product currents and the child-balance obstruction to zero new-hole demands in Lean stdin probes; no new open helper was introduced.
-/
