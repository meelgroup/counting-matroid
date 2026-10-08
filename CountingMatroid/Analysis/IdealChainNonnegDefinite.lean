import CountingMatroid.Analysis.ExchangeProposalGeometry
import Arlib.MarkovChains.Techniques.Dirichlet

set_option autoImplicit false

namespace CountingMatroid.Analysis.IdealChainNonnegDefinite

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ExchangeProposalGeometry
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Holding with probability at least one-half makes a stationary
kernel positive semidefinite, by applying the two-sided bound to 2P-I.
TEXLINE: main.tex:1002-1006 -/
theorem nonnegDefinite_of_holding {Ω : Type} [Fintype Ω]
    (π : FinDist Ω) (P : FinChain Ω) (hst : Stationary π P)
    (hhold : ∀ x, (1 / 2 : ℝ) ≤ P x x) : NonnegDefinite π P := by
  classical
  let R : FinChain Ω := {
    P := fun x y => 2 * P x y - if x = y then 1 else 0
    P_nonneg := by
      intro x y
      by_cases hxy : x = y
      · subst y; simp only [ite_true]; linarith [hhold x]
      · simp only [if_neg hxy, ite_false, sub_zero]
        exact mul_nonneg (by norm_num) (P.coe_nonneg x y)
    P_sum := by
      intro x
      rw [Finset.sum_sub_distrib, ← Finset.mul_sum, P.sum_coe]
      norm_num }
  have hRst : Stationary π R := by
    intro y
    change (∑ x, π x * (2 * P x y - if x = y then 1 else 0)) = π y
    have hcell (x : Ω) : π x * (2 * P x y - if x = y then 1 else 0) =
        2 * (π x * P x y) - if x = y then π x else 0 := by
      split_ifs <;> ring
    simp_rw [hcell]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, hst y]
    simp
    ring
  intro f
  have hform : ip π f (R.act f) = 2 * ip π f (P.act f) - ip π f f := by
    rw [ip_act_eq_sum_sum, ip_act_eq_sum_sum]
    change (∑ x, ∑ y, π x * (2 * P x y - if x = y then 1 else 0) * (f x * f y)) = _
    have hcell (x y : Ω) :
        π x * (2 * P x y - if x = y then 1 else 0) * (f x * f y) =
        2 * (π x * P x y * (f x * f y)) - if x = y then π x * f x * f x else 0 := by
      split_ifs with hxy
      · subst y; ring
      · ring
    simp_rw [hcell, Finset.sum_sub_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_ite_eq, Finset.mem_univ, if_true, ip]
  have hb := neg_ip_le_ip_act_self hRst f
  rw [hform] at hb
  linarith

/-- INTERNAL: Uniform label exchanges hold with probability at least
one-half on every subset, including subsets outside the target support.
TEXLINE: main.tex:746-751 -/
theorem exchange_proposal_holding (n : ℕ) (hn : 0 < n) (state : PairedSet n) :
    (1 / 2 : ℝ) ≤ exchangeProposal n hn state state := by
  classical
  let F : PairedSet n → ℝ := fun next => if next = state then 1 else 0
  have hp := exchange_sum_partition state F
  have hcross : 0 ≤ ∑ a ∈ state, ∑ b ∈ stateᶜ, F (insert b (state.erase a)) := by
    apply Finset.sum_nonneg
    intro a _
    apply Finset.sum_nonneg
    intro b _
    dsimp only [F]
    split_ifs <;> norm_num
  have hcard : (state.card : ℝ) + (stateᶜ.card : ℝ) = 2 * (n : ℝ) := by
    have hc := Finset.card_add_card_compl state
    have hl : Fintype.card (PairedGround n) = 2 * n := by
      simp [PairedGround, Nat.mul_comm]
    rw [hl] at hc
    exact_mod_cast hc
  have hlabels : (Fintype.card (PairedGround n) : ℝ) = 2 * (n : ℝ) := by
    simp [PairedGround]
    ring
  have hproposal : exchangeProposal n hn state state =
      (∑ a : PairedGround n, ∑ b : PairedGround n, F (exchangeState a b state)) /
        (2 * (n : ℝ)) ^ 2 := by
    change (∑ a, ∑ b, if exchangeState a b state = state then
      1 / (Fintype.card (PairedGround n) : ℝ) ^ 2 else 0) = _
    rw [hlabels]
    simp only [Finset.sum_div, F, ite_div, zero_div]
  rw [hproposal, hp]
  dsimp only [F]
  simp only [ite_true, mul_one]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < (2 * (n : ℝ)) ^ 2)).mpr
  dsimp only [F] at hcross
  have hc := congrArg (fun x : ℝ => x ^ 2) hcard
  nlinarith [sq_nonneg ((state.card : ℝ) - (stateᶜ.card : ℝ))]

/-- INTERNAL: The concrete ideal Metropolis chain is PSD on the operational
law, including all zero-weight invalid states.
TEXLINE: main.tex:1002-1006 -/
theorem ideal_chain_nonnegDefinite {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    NonnegDefinite (operationalLaw r o₁ o₂ q w hq hw)
      (idealChain r o₁ o₂ q w hn hq hw) := by
  classical
  apply nonnegDefinite_of_holding _ _ (ideal_chain_stationary r o₁ o₂ q w hn hq hw)
  intro state
  let π := operationalLaw r o₁ o₂ q w hq hw
  let Q := exchangeProposal n hn
  have hsum : Q state state + ∑ next ∈ Finset.univ.erase state, Q state next = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ state)]
    exact Q.sum_coe state
  have hle : (∑ next ∈ Finset.univ.erase state, mhRate π Q state next) ≤
      ∑ next ∈ Finset.univ.erase state, Q state next :=
    Finset.sum_le_sum (fun next _ => mhRate_le_proposal π Q state next)
  have hlazy := exchange_proposal_holding n hn state
  change (1 / 2 : ℝ) ≤ metropolis π Q state state
  rw [metropolis_apply_self, mhStay]
  linarith

end CountingMatroid.Analysis.IdealChainNonnegDefinite
