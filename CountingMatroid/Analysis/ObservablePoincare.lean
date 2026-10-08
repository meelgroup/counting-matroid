import CountingMatroid.Analysis.ObservableProjection

set_option autoImplicit false

/-!
The paper's observable Poincare estimate for the concrete operational law.
The energy identity below handles zero target weights explicitly. The
quantitative transport estimate is an independent same-paper obligation;
stationarity alone does not establish it.
-/

namespace CountingMatroid.Analysis.ObservablePoincare

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
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
  rw [Var_eq_pair, ideal_dirichlet_min_weights r o₁ o₂ q w hn hq hw H]
  -- CONCRETE ROUTE: the pair variance and symmetric-conductance identities
  -- reduce the estimate to weighted transport between transversal values
  -- and defect conditional means. A cellwise comparison is unavailable:
  -- exchangeProposal vanishes on non-neighboring states, whereas their
  -- projected-variance cells can be positive. The paper supplies transport
  -- through paths instead. Its two precise prerequisites are
  -- main.tex:784-857 (binary conditioning-tree transversal variance) and
  -- main.tex:866-911 (defect-to-transversal conditional-mean transport).
  -- Those require the conditional coefficient inequalities and transport
  -- construction from the earlier paper sections, not stationarity.
  -- SAME-PAPER OBLIGATION: no borrowed assumption is proposed.
  sorry

end CountingMatroid.Analysis.ObservablePoincare
