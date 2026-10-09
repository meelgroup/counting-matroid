import CountingMatroid.Analysis.ConditionalDefectCoefficients
import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.OnePairObservablePoincare
import CountingMatroid.Analysis.BalancedCliqueEnergy

set_option autoImplicit false

/-!
The slot-transport specialization for a conditioning-tree split. Its
finite conditional means and restricted energy are defined here. Clearing
the two positive child totals reduces the node estimate to the paper's
singleton-slot transport inequality. The one-pair branch is proved using
the balanced leaf-clique estimate. The general recursion remains open.
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
  -- Concrete route: main.tex:490-492, with singleton multipliers 1 and
  -- ordinary-slot multipliers w_(t,k). The coefficient cancellation and
  -- the one-pair case above are proved. BalancedCliqueEnergy supplies the
  -- potential estimate for every balanced leaf clique.
  -- STILL OPEN (missing local lemma): assemble the balanced-hole recursion
  -- across all ordinary slots. Its invariant must preserve old-hole values,
  -- introduce opposite new-hole values, bound the total leaf demand cost
  -- by 1/s₀ + 1/s₁ + 2*V/(s₀*s₁), and identify the summed leaf pairing with
  -- the two conditional means. The final energy comparison must prove
  -- that leaf exchange edges are disjoint and respect σ.
  -- DefectSlotSplitSignature.slot_split_control gives the local split input;
  -- DefectSlotConservation.future_form_conserved gives future-form
  -- conservation in the companion transport development. Neither supplies
  -- the all-stage recursion or its conditional-transversal specialization.
  -- Abandoned route 1: the direct product of the two endpoint laws has the
  -- right divergence but is nonzero on nonexchange pairs. A Lean stdin
  -- probe verified proposal zero from {(0,false),(1,false)} to
  -- {(0,true),(1,true)} on n=2, so the flow support condition fails.
  -- Abandoned route 2: applying the leaf bound independently while keeping
  -- new-hole demand zero fails child balance. Root totals (3,3), demands
  -- (1/3,-1/3), and child totals (2,1) give child demand 1/3, not zero.
  -- The paper's recursively introduced hole demands are essential.
  sorry

end CountingMatroid.Analysis.ConditionalTransversalSplitTransport

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · proved the n = 1 branch through the separately proved balanced leaf-clique pairing bound; retained the exact theorem interface and positive-total coefficient cancellation. The n ≥ 2 branch needs the all-stage balanced-demand recursion, ordinary-hole cancellation, and disjoint leaf-edge charge. Verified the zero-proposal obstruction to product currents and the child-balance obstruction to zero new-hole demands in Lean stdin probes; no new open helper was introduced.
-/
