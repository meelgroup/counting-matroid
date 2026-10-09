import CountingMatroid.Analysis.SelectedPairedBijection
import CountingMatroid.Analysis.ExchangeProposalGeometry

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The ideal Metropolis kernel in the program's selection-index coordinates.
Rejected proposals contribute to the diagonal, including proposals of weight zero. -/
namespace CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Model
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.SelectedPairedBijection
open Arlib.MarkovChains

/-- INTERNAL: Mass of one accept/reject decision at a proposed state. -/
noncomputable def exchangeOutcome {α : Type} [DecidableEq α]
    (state candidate next : α) (accept : ℝ) : ℝ :=
  accept * (if candidate = next then 1 else 0) +
    (1 - accept) * (if state = next then 1 else 0)

/-- INTERNAL: Proposing the current state always returns it, independently
of the acceptance factor. -/
theorem exchange_outcome_self {α : Type} [DecidableEq α]
    (state next : α) (accept : ℝ) :
    exchangeOutcome state state next accept = if state = next then 1 else 0 := by
  by_cases h : state = next <;> simp [exchangeOutcome, h]

/-- INTERNAL: The library Metropolis chain is the full accept/reject proposal
average, with its rejected mass assigned to the original state. -/
theorem metropolis_outcome_average {α : Type} [Fintype α] [DecidableEq α]
    (π : FinDist α) (Q : FinChain α) (state next : α) :
    metropolis π Q state next = ∑ candidate : α,
      Q state candidate * exchangeOutcome state candidate next
        (min 1 (π candidate / π state)) := by
  classical
  have hsum : (∑ candidate : α, Q state candidate *
      exchangeOutcome state candidate next (min 1 (π candidate / π state))) =
      mhRate π Q state next +
        (if state = next then 1 - ∑ candidate : α, mhRate π Q state candidate else 0) := by
    simp only [exchangeOutcome, mul_add, Finset.sum_add_distrib]
    have hfirst : (∑ candidate : α, Q state candidate *
        (min 1 (π candidate / π state) * (if candidate = next then 1 else 0))) =
        mhRate π Q state next := by
      simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
        Finset.mem_univ, if_true, mhRate_apply]
    rw [hfirst]
    congr 1
    by_cases h : state = next
    · simp only [h, if_true, mul_one, mul_sub, mul_one,
        Finset.sum_sub_distrib, Q.sum_coe, mhRate_apply]
    · simp [h]
  rw [hsum]
  by_cases h : state = next
  · subst next
    rw [metropolis_apply_self, if_pos rfl, mhStay]
    have he := Finset.add_sum_erase (Finset.univ : Finset α)
      (fun candidate => mhRate π Q state candidate) (Finset.mem_univ state)
    linarith
  · rw [metropolis_apply_of_ne π Q h, if_neg h, add_zero]

/-- INTERNAL: The ideal chain is one-half holding plus the indexed
occupied/unoccupied accept/reject average used by the executable step.
TEXLINE: main.tex:746-751 -/
theorem selected_metropolis_kernel {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n) :
    idealChain r o₁ o₂ q weights hn hq hw state next =
      (1 / 2 : ℝ) * (if state = next then 1 else 0) +
      (1 / (2 * (n : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
        exchangeOutcome state
          (insert (selectedLabel state false hcard j).val
            (state.erase (selectedLabel state true hcard i).val)) next
          (min 1 ((operationalLaw r o₁ o₂ q weights hq hw)
            (insert (selectedLabel state false hcard j).val
              (state.erase (selectedLabel state true hcard i).val)) /
            (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  classical
  let π := operationalLaw r o₁ o₂ q weights hq hw
  let F := fun candidate => exchangeOutcome state candidate next
    (min 1 (π candidate / π state))
  change metropolis π (exchangeProposal n hn) state next = _
  rw [metropolis_outcome_average,
    ExchangeProposalGeometry.exchange_proposal_average n hn state hcard F]
  dsimp only [F]
  rw [exchange_outcome_self]
  congr 2
  have houter := select_paired_sum state true hcard
    (fun a => ∑ b ∈ stateᶜ, F (insert b (state.erase a)))
  simp only [if_true] at houter
  rw [← houter]
  apply Finset.sum_congr rfl
  intro i _
  have hinner := select_paired_sum state false hcard
    (fun b => F (insert b (state.erase (selectedLabel state true hcard i).val)))
  simpa only [Bool.false_eq_true, if_false] using hinner.symm

end CountingMatroid.Analysis.SelectedMetropolisKernel
