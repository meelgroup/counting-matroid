import CountingMatroid.Analysis.ObservablePoincare
import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.FinitePhaseEstimationBound
import CountingMatroid.Analysis.StationaryCovarianceSum
import CountingMatroid.Analysis.StationaryPathMoment
import CountingMatroid.Analysis.ObservableEnergyDual
import CountingMatroid.Analysis.IdealChainNonnegDefinite

set_option autoImplicit false

/-!
The stationary correlated-average estimate needed by the finite-suffix MSE
bound. Trajectories use the concrete ideal exchange kernel and all original
operational observables, including diagonal indices and zero-weight states.
The finite product includes one final unused transition; summing it out gives
exactly N observations beginning at the stationary starting state.
A finite geometric action sum proves the covariance bound without requiring
a resolvent, full support, or irreducibility on the extended state space.
-/

namespace CountingMatroid.Analysis.StationaryObservableMSE

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.PhaseObservationExperiment
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Select the real operational observable by the same index used
by empiricalMean and observableMean.
TEXLINE: main.tex:1238-1255 -/
noncomputable def operationalObservable {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (index : Observable n) :
    PairedSet n → ℝ :=
  match index with
  | .inl false => typeIndicator .transversal
  | .inl true => numeratorObservable r o₁ o₂ ρ
  | .inr (i, k) => typeIndicator (if i = k then .transversal else .defect i k)

/-- INTERNAL: Each operational observable takes values in the unit interval.
This includes the repeated diagonal type indicator.
TEXLINE: main.tex:1238-1240 -/
theorem operational_observable_bounds {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (index : Observable n) (state : PairedSet n) :
    0 ≤ operationalObservable r o₁ o₂ ρ index state ∧
      operationalObservable r o₁ o₂ ρ index state ≤ 1 := by
  have hρreal : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
  have hρrealone : (ρ : ℝ) ≤ 1 := by exact_mod_cast hρone
  cases index with
  | inl b =>
      cases b with
      | false =>
          simp only [operationalObservable, typeIndicator]
          split_ifs <;> norm_num
      | true =>
          simp only [operationalObservable, numeratorObservable]
          split_ifs
          · exact ⟨pow_nonneg hρreal _, pow_le_one₀ hρreal hρrealone⟩
          · norm_num
  | inr pair =>
      simp only [operationalObservable, typeIndicator]
      split_ifs <;> norm_num

/-- INTERNAL: The stationary variance term in the time-average bound is
at most one, from the operational observables' unit-interval bounds.
TEXLINE: main.tex:1238-1255 -/
theorem operational_observable_variance_le_one {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (index : Observable n) (π : FinDist (PairedSet n)) :
    Var π (operationalObservable r o₁ o₂ ρ index) ≤ 1 := by
  apply (Var_le_ip_self π _).trans
  rw [ip_self_eq_Ex_sq]
  calc
    _ ≤ Ex π (fun _ => (1 : ℝ)) := by
      apply Ex_mono
      intro state
      obtain ⟨hlower, hupper⟩ :=
        operational_observable_bounds r o₁ o₂ ρ hρ hρone index state
      nlinarith
    _ = 1 := Ex_const π 1

/-- INTERNAL: A finite stationary path second moment, including a final
unused transition. This keeps all covariances between observations rather
than replacing them by independent samples.
TEXLINE: main.tex:982-1013 -/
noncomputable def trajectorySquaredMoment {Ω : Type} [Fintype Ω]
    (π : FinDist Ω) (P : FinChain Ω) (G : Ω → ℝ) (N : ℕ) : ℝ :=
  ∑ path : Fin (N + 1) → Ω,
    (π (path 0) * ∏ i : Fin N, P (path i.castSucc) (path i.succ)) *
      ((∑ i : Fin N, G (path i.castSucc)) / (N : ℝ) - Ex π G) ^ 2

/-- INTERNAL: Good current multipliers are strictly positive at a positive
schedule parameter, including the empty defect-index case.
TEXLINE: main.tex:733-735 -/
theorem good_current_weights_pos (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (current : AnnealingCursor n)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current) :
    ∀ index, 0 < current.currentWeights index := by
  intro index
  have hρ := (AnnealingPartitionDrift.schedule_power_lower n p hn).1
  have hC := (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
  have hD := DefectPartitionPositive.defect_partition_pos r o₁ o₂
    ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) (pow_pos hρ j) index
  exact (div_pos (div_pos hC hD) (by norm_num : (0 : ℚ) < 4)).trans_le
    (hgood.2 index).1

/-- INTERNAL: Express the stationary moment at a fixed current phase cursor.
Positivity arguments are proofs only; no extra oracle or randomness is added.
TEXLINE: main.tex:1241-1255 -/
noncomputable def stationaryObservationMoment (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (j : ℕ) (current : AnnealingCursor n)
    (hw : ∀ index, 0 < current.currentWeights index) (index : Observable n) : ℝ :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  trajectorySquaredMoment
    (operationalLaw r o₁ o₂ (s.ρ ^ j) current.currentWeights hq hw)
    (idealChain r o₁ o₂ (s.ρ ^ j) current.currentWeights hn hq hw)
    (operationalObservable r o₁ o₂ s.ρ index) s.observations

/-- INTERNAL: The stationary real observable mean agrees with the rational
mean used in the completed finite-tape squared error.
TEXLINE: main.tex:1241-1247 -/
theorem operational_observable_mean (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (current : AnnealingCursor n)
    (hw : ∀ index, 0 < current.currentWeights index) (index : Observable n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    Ex (operationalLaw r o₁ o₂ (s.ρ ^ j) current.currentWeights hq hw)
      (operationalObservable r o₁ o₂ s.ρ index) =
      (observableMean r o₁ o₂ s j current index : ℝ) := by
  dsimp only
  cases index with
  | inl b =>
      cases b with
      | false => exact operational_type_mean r o₁ o₂ _ _ _ hw .transversal
      | true => exact operational_numerator_mean r o₁ o₂ _ _ _ _ hw
  | inr pair =>
      rcases pair with ⟨i, k⟩
      exact operational_type_mean r o₁ o₂ _ _ _ hw
        (if i = k then .transversal else .defect i k)

/-- INTERNAL: Apply the paper's stationary restricted-Poincare time-average
estimate to each concrete observable. The factor 4000 is twice the observable
Poincare constant 2000, with stationary variance bounded by one.
TEXLINE: main.tex:972-1013,1238-1255 -/
theorem stationary_observation_mse (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (j : ℕ) (current : AnnealingCursor n)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (hw : ∀ index, 0 < current.currentWeights index) (index : Observable n) :
    stationaryObservationMoment n r o₁ o₂ p hn j current hw index ≤
      4000 * (n : ℝ) ^ 6 /
        (CountingMatroid.Interface.Pseudocode.setup n p).observations := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hρ := AnnealingPartitionDrift.schedule_power_lower n p hn
  have hq : 0 < s.ρ ^ j := pow_pos hρ.1 j
  have hqone : s.ρ ^ j ≤ 1 := pow_le_one₀ hρ.1.le hρ.2.1
  let π := operationalLaw r o₁ o₂ (s.ρ ^ j) current.currentWeights hq hw
  let P := idealChain r o₁ o₂ (s.ρ ^ j) current.currentWeights hn hq hw
  let G := operationalObservable r o₁ o₂ s.ρ index
  let K : ℝ := 2000 * (n : ℝ) ^ 6
  have henergy : ∀ H, Var π (ObservableProjection.observableProjection π H) ≤
      K * dirichlet π P H H := fun H =>
    ObservablePoincare.observable_poincare n r M₁ M₂ o₁ o₂ (s.ρ ^ j)
      current.currentWeights hn hfull hr h₁ h₂ hq hqone hw hgood.2 H
  have hvariance : Var π G ≤ 1 := operational_observable_variance_le_one
    r o₁ o₂ s.ρ hρ.1.le hρ.2.1 index π
  have hfiber : ∃ c : Fin n → Fin n → ℝ,
      ∀ a b state, (classifyState state).val = .defect a b → G state = c a b := by
    dsimp only [G]
    cases index with
    | inl b =>
      refine ⟨fun _ _ => 0, ?_⟩
      intro a k state hk
      cases b <;> simp [operationalObservable, typeIndicator, numeratorObservable, hk]
    | inr pair =>
      rcases pair with ⟨i, k⟩
      refine ⟨fun a b => if StateKind.defect a b =
        (if i = k then .transversal else .defect i k) then 1 else 0, ?_⟩
      intro a b state hk
      simp only [operationalObservable, typeIndicator, hk]
  obtain ⟨c, hc⟩ := hfiber
  let C := K * Var π G
  have hdual : ∀ H, (ip π (fun x => G x - Ex π G) H) ^ 2 ≤
      C * dirichlet π P H H :=
    ObservableEnergyDual.observable_energy_dual r o₁ o₂ (s.ρ ^ j)
      current.currentWeights hq hw P G c hc K henergy
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hC : 0 ≤ C := mul_nonneg hK (Var_nonneg π G)
  have hrev : Reversible π P := metropolis_reversible_zero_weights _ _
    (exchange_proposal_symmetric n hn)
  have hpsd : NonnegDefinite π P := IdealChainNonnegDefinite.ideal_chain_nonnegDefinite
    r o₁ o₂ (s.ρ ^ j) current.currentWeights hn hq hw
  have hcov := StationaryCovarianceSum.covariance_sum_le hrev hpsd
    (fun x => G x - Ex π G) C hC hdual
  have hN : 0 < s.observations :=
    (FinitePhaseEstimationBound.schedule_estimation_budget n p hn).2.1
  have hbound := StationaryPathMoment.stationary_average_le_of_covariance
    π P hrev.stationary G C hcov s.observations hN
  change trajectorySquaredMoment π P G s.observations ≤ _
  calc
    _ ≤ 2 * C / (s.observations : ℝ) := hbound
    _ ≤ 4000 * (n : ℝ) ^ 6 / (s.observations : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      have hb := mul_le_mul_of_nonneg_left hvariance (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hK)
      dsimp only [C, K] at *
      nlinarith

end CountingMatroid.Analysis.StationaryObservableMSE

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · proved · replaced the inverse/infinite-series step by a finite geometric covariance bound; proved weighted projection orthogonality, ideal-chain PSD, and the exact product-path second-moment recurrence in four support modules.
* r24 · open · extracted the projected energy estimate and bounded each observable's variance by one; exact? exhausted the heartbeat limit, and no correlated product-path covariance estimate was found in Arlib or Mathlib. The first live child handoff was mechanically rejected without further diagnostic.
-/
