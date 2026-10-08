import CountingMatroid.Analysis.StationaryMeanIdentities
import Arlib.MarkovChains.Chains.Metropolis
import Arlib.Probability.FinDistFunctional

set_option autoImplicit false

namespace CountingMatroid.Analysis.IdealExchangeChain

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open Arlib.Probability Arlib.MarkovChains

/-- INTERNAL: Relabel a paired state by swapping two ground labels. On an
n-element state a uniformly drawn ordered pair of labels gives the paper's
lazy exchange proposal: equal occupancy holds, and unequal occupancy exchanges.
The separate operational coupling still has to identify its transition law.
TEXLINE: main.tex:746-751 -/
def exchangeState {n : ℕ} (a b : PairedGround n) (state : PairedSet n) : PairedSet n :=
  state.image (Equiv.swap a b)

/-- INTERNAL: A label exchange is an involution on the finite state space. -/
theorem exchange_state_involutive {n : ℕ} (a b : PairedGround n)
    (state : PairedSet n) : exchangeState a b (exchangeState a b state) = state := by
  unfold exchangeState
  rw [Finset.image_image]
  simp only [Function.comp_def, Equiv.swap_apply_self, Finset.image_id']

/-- INTERNAL: Each fixed exchange has a symmetric transition indicator. -/
theorem exchange_state_eq_iff {n : ℕ} (a b : PairedGround n)
    (state next : PairedSet n) : exchangeState a b state = next ↔
      exchangeState a b next = state := by
  constructor <;> intro h
  · rw [← h, exchange_state_involutive]
  · rw [← h, exchange_state_involutive]

/-- INTERNAL: Ideal proposal obtained from two independent uniform paired
labels, including equal labels and equal occupancy. It is defined on all
paired subsets; the Metropolis target rejects zero-weight invalid states.
TEXLINE: main.tex:746-751 -/
noncomputable def exchangeProposal (n : ℕ) (hn : 0 < n) : FinChain (PairedSet n) where
  P state next := ∑ a : PairedGround n, ∑ b : PairedGround n,
    if exchangeState a b state = next then
      1 / (Fintype.card (PairedGround n) : ℝ) ^ 2 else 0
  P_nonneg state next := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    split_ifs <;> positivity
  P_sum state := by
    rw [Finset.sum_comm]
    apply Eq.trans (Finset.sum_congr rfl (fun a _ => Finset.sum_comm))
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul]
    have hcard : (Fintype.card (PairedGround n) : ℝ) ≠ 0 := by
      simp only [PairedGround, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
      exact_mod_cast (by omega : n * 2 ≠ 0)
    field_simp

/-- INTERNAL: The concrete ideal exchange proposal is symmetric, since
swapping a fixed pair of labels is an involution. -/
theorem exchange_proposal_symmetric (n : ℕ) (hn : 0 < n)
    (state next : PairedSet n) :
    exchangeProposal n hn state next = exchangeProposal n hn next state := by
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  simp only [exchange_state_eq_iff]

/-- INTERNAL: Operational weights are nonnegative at a positive parameter
with positive multipliers, including zero on rejected classifier branches. -/
theorem state_weight_nonneg {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (state : PairedSet n) : 0 ≤ stateWeight r o₁ o₂ q w state := by
  classical
  cases hk : (classifyState state).val with
  | invalid => simp [stateWeight, hk, weightOfKind]
  | transversal =>
    simp only [stateWeight, hk, weightOfKind, Arlib.Computation.Charged.val_bind,
      CountingMatroid.Model.Operations.natSub,
      Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure,
      BoundedRunResourceEnvelope.ratPower_value, Option.getD_some]
    exact (pow_pos hq _).le
  | defect i k =>
    by_cases h : i ≠ k
    · simp only [stateWeight, hk, weightOfKind, dif_pos h,
        Arlib.Computation.Charged.val_bind, CountingMatroid.Model.Operations.natSub,
        CountingMatroid.Model.Operations.multiplierRead,
        CountingMatroid.Model.Operations.ratMul,
        Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany,
        Arlib.Computation.Charged.val_pure,
        BoundedRunResourceEnvelope.ratPower_value, Option.getD_some]
      exact (mul_pos (hw ⟨i, k, h⟩) (pow_pos hq _)).le
    · simp [stateWeight, hk, weightOfKind, h]

/-- INTERNAL: Normalize the actual rational state weights as a finite real
probability distribution for the library's Markov-chain API. -/
noncomputable def operationalLaw {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    FinDist (PairedSet n) where
  p state := (stateWeight r o₁ o₂ q w state : ℝ) / (normalizer r o₁ o₂ q w : ℝ)
  p_nonneg state := by
    apply div_nonneg
    · exact_mod_cast state_weight_nonneg r o₁ o₂ q w hq hw state
    · exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 w hq hw).1.le
  p_sum := by
    rw [← Finset.sum_div]
    have hsum : (∑ state : PairedSet n, (stateWeight r o₁ o₂ q w state : ℝ)) =
        (normalizer r o₁ o₂ q w : ℝ) := by
      unfold normalizer
      norm_cast
    rw [hsum]
    apply div_self
    exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 w hq hw).1.ne'

/-- INTERNAL: Metropolis detailed balance also holds for targets with zero
weights. This permits extending the valid-state law by zero to all paired
subsets without imposing an artificial full-support assumption. -/
theorem metropolis_reversible_zero_weights {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : FinDist Ω) (Q : FinChain Ω) (hsymm : ∀ x y, Q x y = Q y x) :
    Reversible μ (metropolis μ Q) := by
  intro x y
  by_cases hxy : x = y
  · subst y
    rfl
  rw [metropolis_apply_of_ne μ Q hxy, metropolis_apply_of_ne μ Q (Ne.symm hxy)]
  by_cases hx : μ x = 0
  · simp [mhRate_apply, hx]
  by_cases hy : μ y = 0
  · simp [mhRate_apply, hy]
  have hxpos : 0 < μ x := lt_of_le_of_ne (μ.coe_nonneg x) (Ne.symm hx)
  have hypos : 0 < μ y := lt_of_le_of_ne (μ.coe_nonneg y) (Ne.symm hy)
  rw [mhRate_detailed_balance Q y hxpos, mhRate_detailed_balance Q x hypos,
    hsymm x y, min_comm]

/-- INTERNAL: The fixed ideal exchange Metropolis kernel at the operational
state weights. Invalid-state targets have zero mass and are rejected; the
separate finite-tape coupling concerns draws realizing its acceptance rates.
TEXLINE: main.tex:746-757,1207-1212 -/
noncomputable def idealChain {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) : FinChain (PairedSet n) :=
  metropolis (operationalLaw r o₁ o₂ q w hq hw) (exchangeProposal n hn)

/-- INTERNAL: The normalized operational law is stationary for its concrete
ideal exchange kernel, including zero mass on invalid states.
TEXLINE: main.tex:746-757 -/
theorem ideal_chain_stationary {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) :
    Stationary (operationalLaw r o₁ o₂ q w hq hw)
      (idealChain r o₁ o₂ q w hn hq hw) :=
  (metropolis_reversible_zero_weights _ _ (exchange_proposal_symmetric n hn)).stationary

/-- INTERNAL: The real-valued type indicator used by the ideal-chain
analysis is the same classifier observation counted by the program.
TEXLINE: main.tex:1181-1187,1238-1247 -/
noncomputable def typeIndicator {n : ℕ} (kind : StateKind n) (state : PairedSet n) : ℝ :=
  if (classifyState state).val = kind then 1 else 0

/-- INTERNAL: Identify the operational rational type mean with expectation
under the concrete ideal stationary law, for correlated-observation analysis.
TEXLINE: main.tex:1241-1247 -/
theorem operational_type_mean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (kind : StateKind n) :
    Ex (operationalLaw r o₁ o₂ q w hq hw) (typeIndicator kind) =
      (typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  unfold Ex typeMean
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hk : (classifyState state).val = kind
  · simp [operationalLaw, typeIndicator, hk]
  · simp [operationalLaw, typeIndicator, hk]

/-- INTERNAL: The real-valued annealing numerator observed by the program;
it vanishes on defects and retains the cooling factor on transversals.
TEXLINE: main.tex:1181-1187,1238-1247 -/
noncomputable def numeratorObservable {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (state : PairedSet n) : ℝ :=
  if (classifyState state).val = .transversal then
    (ρ : ℝ) ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
  else 0

/-- INTERNAL: The operational numerator mean is the expectation of the
annealing observable under the ideal stationary law.
TEXLINE: main.tex:1241-1247 -/
theorem operational_numerator_mean {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q ρ : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    Ex (operationalLaw r o₁ o₂ q w hq hw) (numeratorObservable r o₁ o₂ ρ) =
      (numeratorMean r o₁ o₂ q ρ w : ℝ) := by
  classical
  unfold Ex numeratorMean
  push_cast
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hk : (classifyState state).val = .transversal
  · simp [operationalLaw, numeratorObservable, hk, div_mul_eq_mul_div]
  · simp [operationalLaw, numeratorObservable, hk]

end CountingMatroid.Analysis.IdealExchangeChain
