import CountingMatroid.Analysis.ObservableProjection
import CountingMatroid.Analysis.ObservableVarianceDecomposition
import CountingMatroid.Analysis.TransversalEventMean
import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.OnePairObservablePoincare
import CountingMatroid.Analysis.TransversalVarianceBound
import CountingMatroid.Analysis.DefectMeanExchangeFlow

set_option autoImplicit false

/-!
The paper's observable Poincare estimate for the concrete operational law.
The energy identity below handles zero target weights explicitly. The
quantitative transport and transversal estimates are independent same-paper
obligations in DefectMeanExchangeFlow and TransversalVarianceBound;
stationarity alone does not establish them. The defect-mean step is reduced
to an exchange-supported signed current with prescribed conditional-mean
divergence and a normalized energy bound. Its summation-by-parts and
Cauchy--Schwarz implications are proved in ExchangeFlowEnergy. The one-pair
boundary case is closed outright using the constant-two estimate in
OnePairObservablePoincare.
-/

namespace CountingMatroid.Analysis.ObservablePoincare

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Write the ideal Metropolis energy using symmetric proposal
conductances, including the zero-weight invalid states.
TEXLINE: main.tex:759-768 -/
theorem ideal_dirichlet_min_weights {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    dirichlet π (idealChain r o₁ o₂ q w hn hq hw) H H =
      (1 / 2 : ℝ) * ∑ state : PairedSet n, ∑ next : PairedSet n,
        exchangeProposal n hn state next * min (π state) (π next) *
          (H state - H next) ^ 2 := by
  classical
  intro π
  rw [dirichlet_self_eq_pair (ideal_chain_stationary r o₁ o₂ q w hn hq hw)]
  congr 1
  apply Finset.sum_congr rfl
  intro state _
  apply Finset.sum_congr rfl
  intro next _
  by_cases heq : state = next
  · subst next
    simp
  change π state * metropolis π (exchangeProposal n hn) state next * _ = _
  rw [metropolis_apply_of_ne π (exchangeProposal n hn) heq]
  by_cases hzero : π state = 0
  · simp only [hzero, zero_mul, min_eq_left (π.coe_nonneg next), mul_zero]
  · rw [mhRate_detailed_balance (exchangeProposal n hn) next
      (lt_of_le_of_ne (π.coe_nonneg state) (Ne.symm hzero))]

/-- INTERNAL: The type-mass lower bound converts the two paper constants
to the stated observable Poincare constant, with the ideal proposal's
normalization retained explicitly.
TEXLINE: main.tex:944-951 -/
theorem observable_poincare_constant_bound (n : ℕ) (hn : 0 < n)
    (p E : ℝ) (hp : 1 / (5 * (n : ℝ) ^ 2) ≤ p) (hE : 0 ≤ E) :
    (72 * (n : ℝ) ^ 2 + 73 * (n : ℝ) + 16) *
        (2 * (n : ℝ) ^ 2 * E / p) ≤ 2000 * (n : ℝ) ^ 6 * E := by
  have hN : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  have hden : 0 < 5 * (n : ℝ) ^ 2 := by positivity
  have hp0 : 0 < p := (div_pos (by norm_num) hden).trans_le hp
  have hp' : 1 ≤ p * (5 * (n : ℝ) ^ 2) := (div_le_iff₀ hden).mp hp
  have hR : 2 * (n : ℝ) ^ 2 * E / p ≤ 10 * (n : ℝ) ^ 4 * E := by
    apply (div_le_iff₀ hp0).mpr
    have h := mul_le_mul_of_nonneg_left hp'
      (by positivity : 0 ≤ 2 * (n : ℝ) ^ 2 * E)
    nlinarith [h]
  have hcoef : 72 * (n : ℝ) ^ 2 + 73 * (n : ℝ) + 16 ≤
      161 * (n : ℝ) ^ 2 := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ (n : ℝ) - 1) (Nat.cast_nonneg n)]
  calc
    _ ≤ (72 * (n : ℝ) ^ 2 + 73 * (n : ℝ) + 16) *
        (10 * (n : ℝ) ^ 4 * E) :=
      mul_le_mul_of_nonneg_left hR (by positivity)
    _ ≤ (161 * (n : ℝ) ^ 2) * (10 * (n : ℝ) ^ 4 * E) :=
      mul_le_mul_of_nonneg_right hcoef (by positivity)
    _ = 1610 * (n : ℝ) ^ 6 * E := by ring
    _ ≤ _ := by nlinarith [mul_nonneg (pow_nonneg (Nat.cast_nonneg n) 6) hE]

/-- PAPER: main.tex:928-951
The observable Poincare inequality for exact matroid-oracle weights and good
multipliers. It controls the energy of the original function, preserving
its fluctuations within each defect fiber on the right-hand side. -/
theorem observable_poincare (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index))
    (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    Var π (observableProjection π H) ≤
      2000 * (n : ℝ) ^ 6 * dirichlet π (idealChain r o₁ o₂ q w hn hq hw) H H := by
  classical
  intro π
  let p₀ := classMass π .transversal
  let m₀ := classMean π H .transversal
  let V := transversalVariance π H
  let E := (1 / 2 : ℝ) * ∑ state : PairedSet n, ∑ next : PairedSet n,
    exchangeProposal n hn state next * min (π state) (π next) *
      (H state - H next) ^ 2
  have hEeq : E = dirichlet π (idealChain r o₁ o₂ q w hn hq hw) H H :=
    (ideal_dirichlet_min_weights r o₁ o₂ q w hn hq hw H).symm
  have hE : 0 ≤ E := by
    rw [hEeq]
    exact dirichlet_self_nonneg (ideal_chain_stationary r o₁ o₂ q w hn hq hw) H
  by_cases hnOne : n = 1
  · subst n
    have hzero : π ∅ = 0 := by
      have hk : (classifyState (∅ : PairedSet 1)).val = .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk, weightOfKind]
    have hfullmass : π {(0, false), (0, true)} = 0 := by
      have hk : (classifyState ({(0, false), (0, true)} : PairedSet 1)).val = .invalid := by decide
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk, weightOfKind]
    have htwo := OnePairObservablePoincare.one_pair_observable_poincare π hzero hfullmass H
    change Var π (observableProjection π H) ≤ 2 * E at htwo
    have hbound : Var π (observableProjection π H) ≤ 2000 * E :=
      htwo.trans (by nlinarith [hE])
    simpa only [Nat.cast_one, one_pow, mul_one, hEeq] using hbound
  have hp : 1 / (5 * (n : ℝ) ^ 2) ≤ p₀ := by
    dsimp only [p₀, π]
    rw [operational_class_mass]
    have hmass := (TypeMassLowerBounds.good_type_mass_bounds
      r o₁ o₂ q w hn hq hgood).2.1
    have hcast := (Rat.cast_le (K := ℝ)).mpr hmass
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hcast
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hp₀ : 0 < p₀ := (div_pos (by norm_num) (by positivity)).trans_le hp
  let κ := fun state next : PairedSet n =>
    exchangeProposal n hn state next * min (π state) (π next)
  have hκ : ∀ state next, 0 ≤ κ state next := fun state next =>
    mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
      (le_min (π.coe_nonneg state) (π.coe_nonneg next))
  have hpotential : potentialEnergy κ H = E := rfl
  let R := 2 * (n : ℝ) ^ 2 * E / p₀
  choose a b hlarge using (fun i k : Fin n => large_pair_event π i k)
  -- Choose the large two-pair event before asking for transport. Event
  -- selection and its conditional-mean variance bound are already proved.
  -- R is the paper's normalization D(H)/c₀ = 2n² E(H)/π(Ω₀).
  suffices hpaper :
      V ≤ (n : ℝ) * (1 + 8 * (n : ℝ)) * R ∧
      ∀ i k : Fin n, i ≠ k →
        (classMean π H (.defect i k) -
          eventMean π H (pairEvent i k (a i k) (b i k))) ^ 2 ≤
          (8 + 32 * (n : ℝ)) * R by
    obtain ⟨htrans, htransport⟩ := hpaper
    have hdef (i k : Fin n) (hik : i ≠ k) :
        (classMean π H (.defect i k) - m₀) ^ 2 ≤
          2 * (8 + 32 * (n : ℝ)) * R + 8 * V := by
      have hevent := large_pair_event_mean_bound π H i k (a i k) (b i k)
        hp₀ (hlarge i k)
      change (eventMean π H (pairEvent i k (a i k) (b i k)) - m₀) ^ 2 ≤
        4 * V at hevent
      have ht := htransport i k hik
      nlinarith [sq_nonneg (classMean π H (.defect i k) + m₀ -
        2 * eventMean π H (pairEvent i k (a i k) (b i k)))]
    have hV : 0 ≤ V := transversal_variance_nonneg π H
    have hR : 0 ≤ R := by dsimp [R]; positivity
    let B := 2 * (8 + 32 * (n : ℝ)) * R + 8 * V
    have hB : 0 ≤ B := by dsimp [B]; positivity
    have hmass : (∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k)) ≤ 1 := by
      have hpart := class_mass_partition π
      have hinvalid : classMass π .invalid = 0 :=
        operational_invalid_mass_zero r o₁ o₂ q w hq hw
      rw [hinvalid] at hpart
      have hpos := class_mass_nonneg π .transversal
      linarith
    have hdefsum : (∑ i : Fin n, ∑ k : Fin n,
        classMass π (.defect i k) * (classMean π H (.defect i k) - m₀) ^ 2) ≤ B := by
      calc
        _ ≤ ∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k) * B := by
          apply Finset.sum_le_sum
          intro i _
          apply Finset.sum_le_sum
          intro k _
          by_cases hik : i = k
          · subst k
            have hz : classMass π (.defect i i) = 0 :=
              diagonal_class_mass_zero r o₁ o₂ q w hq hw i
            simp [hz]
          · exact mul_le_mul_of_nonneg_left (hdef i k hik)
              (class_mass_nonneg π (.defect i k))
        _ = (∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k)) * B := by
          simp only [Finset.sum_mul]
        _ ≤ B := by
          simpa only [one_mul] using mul_le_mul_of_nonneg_right hmass hB
    have hmoment : (∑ state : PairedSet n,
        if (classifyState state).val = .transversal then
          π state * (H state - m₀) ^ 2 else 0) = p₀ * V := by
      change _ = p₀ * ((∑ state : PairedSet n,
        if (classifyState state).val = .transversal then
          π state * (H state - m₀) ^ 2 else 0) / p₀)
      field_simp [hp₀.ne']
    have hvar := observable_variance_decomposition r o₁ o₂ q w hq hw H m₀
    dsimp only at hvar
    rw [hmoment] at hvar
    have hweighted : p₀ * V ≤ V := by
      simpa only [one_mul] using
        mul_le_mul_of_nonneg_right (class_mass_le_one π .transversal) hV
    calc
      Var π (observableProjection π H) ≤ p₀ * V +
          ∑ i : Fin n, ∑ k : Fin n,
            classMass π (.defect i k) * (classMean π H (.defect i k) - m₀) ^ 2 := hvar
      _ ≤ V + B := add_le_add hweighted hdefsum
      _ = 9 * V + 2 * (8 + 32 * (n : ℝ)) * R := by dsimp [B]; ring
      _ ≤ 9 * ((n : ℝ) * (1 + 8 * (n : ℝ)) * R) +
          2 * (8 + 32 * (n : ℝ)) * R :=
        add_le_add (mul_le_mul_of_nonneg_left htrans (by norm_num : (0 : ℝ) ≤ 9)) le_rfl
      _ = (72 * (n : ℝ) ^ 2 + 73 * (n : ℝ) + 16) * R := by ring
      _ ≤ 2000 * (n : ℝ) ^ 6 * E := observable_poincare_constant_bound n hn p₀ E hp hE
      _ = _ := by rw [hEeq]
  constructor
  · exact TransversalVarianceBound.transversal_variance_bound
      n r M₁ M₂ o₁ o₂ q w hn hfull hr h₁ h₂ hq hqone hw hgood H
  · intro i k hik
    let A := pairEvent i k (a i k) (b i k)
    -- The paper constructs this current before choosing H. Its cost is
    -- measured using the normalized ideal-exchange conductances κ, so the
    -- conversion from the unnormalized coefficient is exactly 2n²/p₀.
    suffices hflow : ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) A),
        flowEnergy κ flow.current ≤ (8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / p₀) by
      obtain ⟨flow, hcost⟩ := hflow
      have hb := flow.pairing_sq_le hκ
        ((8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / p₀)) hcost H
      rw [conditional_mean_demand_pairing, hpotential] at hb
      change (classMean π H (.defect i k) - eventMean π H A) ^ 2 ≤ _
      calc
        _ ≤ ((8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / p₀)) * E := hb
        _ = (8 + 32 * (n : ℝ)) * R := by dsimp [R]; ring
    exact DefectMeanExchangeFlow.defect_mean_exchange_flow
      n r M₁ M₂ o₁ o₂ q w hn hfull hr h₁ h₂ hq hqone hw hgood
      i k hik (a i k) (b i k) (hlarge i k)

end CountingMatroid.Analysis.ObservablePoincare

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · handoff-rejected · observable-tree-flow-r26-20261008-v2 was also rejected with “mechanical admission rejected; retain all files” after a properly granted targeted Lake build succeeded; all four support files remain owned here, and the two same-paper obligations remain open.

* r26 · handoff-rejected · observable-tree-flow-r26-20261008 was rejected with “mechanical admission rejected; retain all files”; the parent passed standalone elaboration and both child statements elaborated, but the two same-paper proofs remain open and ownership was not transferred.

* r26 · decomposed · closed the n=1 case with constant two and proved the signed-flow energy criterion; the parent now applies separately elaborated TransversalVarianceBound and DefectMeanExchangeFlow, exposing the adaptive variance tree and the balanced-current construction for live parallel handoff.

* r26 · partial · closed the n=1 case with constant two; proved the zero-conductance-safe signed-flow energy criterion and conditional-mean pairing in ExchangeFlowEnergy; the larger-ground defect-transfer branch now asks for the precise current and cost constructed at main.tex:511-709, while the binary-tree transversal estimate remains open.

* r26 · partial · proved the zero-conductance-safe signed-flow energy criterion and conditional-mean pairing in ExchangeFlowEnergy; the defect-transfer branch now asks for the precise current and cost constructed at main.tex:511-709, while the binary-tree transversal estimate remains open.

* current · partial · proved the projection variance decomposition and mass bookkeeping in ObservableVarianceDecomposition, and reduced the original open goal to the paper's transversal variance and defect-mean transport estimates; the normalization and final constants are proved.
-/
