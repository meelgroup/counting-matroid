import CountingMatroid.Analysis.PositiveTimeTraceChain
import CountingMatroid.Analysis.ObservablePoincare
import CountingMatroid.Analysis.IdealChainNonnegDefinite

set_option autoImplicit false

/-!
The paper's trace spectral gap for the concrete ideal exchange chain. The
existing transversal variance estimate is applied to the proved harmonic
extension; no mixing or operational finite-tape comparison is assumed.
-/
namespace CountingMatroid.Analysis.TransversalTraceSpectralGap

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.PositiveTimeTraceChain
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Boundary states of the concrete positive-time trace.
TEXLINE: main.tex:1023-1030 -/
noncomputable def transversalSet (n : ℕ) : Finset (PairedSet n) := by
  classical
  exact Finset.univ.filter (fun x => (classifyState x).val = .transversal)

/-- PAPER: main.tex:1033-1037,1060-1071
The inverse spectral gap of the concrete transversal trace is at most 18n⁴.
Positive boundary weights and boundary mass only supply the trace's subtype
construction; the quantitative estimate follows from transversal variance. -/
theorem transversal_trace_spectral_gap (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ a, 0 < w a)
    (hgood : ∀ a,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q a) / 4 ≤ w a ∧
      w a ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q a))
    (hπ : ∀ x ∈ transversalSet n, 0 < operationalLaw r o₁ o₂ q w hq hw x)
    (hA : 0 < ∑ x ∈ transversalSet n, operationalLaw r o₁ o₂ q w hq hw x) :
    SpectralGapAtLeast (traceLaw (operationalLaw r o₁ o₂ q w hq hw) (transversalSet n) hA)
      (traceChain (operationalLaw r o₁ o₂ q w hq hw)
        (idealChain r o₁ o₂ q w hn hq hw)
        (ideal_chain_stationary r o₁ o₂ q w hn hq hw) (transversalSet n) hπ)
      (1 / (18 * (n : ℝ) ^ 4)) := by
  classical
  let π := operationalLaw r o₁ o₂ q w hq hw
  let P := idealChain r o₁ o₂ q w hn hq hw
  let A := transversalSet n
  let μ := traceLaw π A hA
  let Q := traceChain π P (ideal_chain_stationary r o₁ o₂ q w hn hq hw) A hπ
  have hmass : classMass π .transversal = ∑ x ∈ A, π x := by
    simp [classMass, A, transversalSet, Finset.sum_filter]
  intro f
  let h : PairedSet n → ℝ := fun x => if hx : x ∈ A then f ⟨x, hx⟩ else 0
  let H := harmonicExtension P A h
  have hH (x : A) : H x = f x := by
    dsimp only [H]
    rw [harmonicExtension_on_target P A h x x.property]
    simp only [h, dif_pos x.property]
    rfl
  have hmean : classMean π H .transversal = Ex μ f := by
    unfold classMean
    rw [hmass]
    change (∑ x, if (classifyState x).val = .transversal then π x * H x else 0) /
      (∑ x ∈ A, π x) = _
    rw [← Finset.sum_filter]
    change (∑ x ∈ A, π x * H x) / (∑ x ∈ A, π x) = _
    rw [Finset.sum_subtype A (fun _ => Iff.rfl), Finset.sum_div]
    unfold Ex
    apply Finset.sum_congr rfl
    intro x _
    rw [hH]
    change π x * f x / (∑ z ∈ A, π z) = (π x / (∑ z ∈ A, π z)) * f x
    ring
  have hvar : transversalVariance π H = Var μ f := by
    unfold transversalVariance
    rw [hmean, hmass]
    change (∑ x, if (classifyState x).val = .transversal then
      π x * (H x - Ex μ f) ^ 2 else 0) / (∑ x ∈ A, π x) = _
    rw [← Finset.sum_filter]
    change (∑ x ∈ A, π x * (H x - Ex μ f) ^ 2) / (∑ x ∈ A, π x) = _
    rw [Finset.sum_subtype A (fun _ => Iff.rfl), Finset.sum_div, Var_apply]
    apply Finset.sum_congr rfl
    intro x _
    rw [hH]
    change π x * (f x - Ex μ f) ^ 2 / (∑ z ∈ A, π z) =
      (π x / (∑ z ∈ A, π z)) * (f x - Ex μ f) ^ 2
    ring
  have hv := TransversalVarianceBound.transversal_variance_bound n r M₁ M₂ o₁ o₂
    q w hn hfull hr h₁ h₂ hq hqone hw hgood H
  have hE : ExchangeFlowEnergy.potentialEnergy
      (fun x y => exchangeProposal n hn x y * min (π x) (π y)) H =
      dirichlet π P H H := by
    symm
    exact ObservablePoincare.ideal_dirichlet_min_weights r o₁ o₂ q w hn hq hw H
  change transversalVariance π H ≤ _ at hv
  rw [hvar, hE, hmass, trace_chain_energy π P
    (ideal_chain_stationary r o₁ o₂ q w hn hq hw) A hπ hA h] at hv
  have hm : (∑ x ∈ A, π x) ≠ 0 := hA.ne'
  have hcancel : 2 * (n : ℝ) ^ 2 * ((∑ x ∈ A, π x) * dirichlet μ Q f f) /
      (∑ x ∈ A, π x) = 2 * (n : ℝ) ^ 2 * dirichlet μ Q f f := by
    field_simp [hm]
  have hrestrict : (fun x : A => h x) = f := by
    funext x
    simp only [h, dif_pos x.property]
    rfl
  rw [hrestrict] at hv
  change Var μ f ≤ (n : ℝ) * (1 + 8 * (n : ℝ)) *
    (2 * (n : ℝ) ^ 2 * ((∑ x ∈ A, π x) * dirichlet μ Q f f) / (∑ x ∈ A, π x)) at hv
  rw [hcancel] at hv
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hcoef : (n : ℝ) * (1 + 8 * (n : ℝ)) * (2 * (n : ℝ) ^ 2) ≤ 18 * (n : ℝ) ^ 4 := by
    nlinarith [mul_nonneg (by positivity : 0 ≤ (n : ℝ) ^ 3)
      (by linarith : 0 ≤ (n : ℝ) - 1)]
  have hrev : Reversible π P :=
    metropolis_reversible_zero_weights π (exchangeProposal n hn) (exchange_proposal_symmetric n hn)
  have hQrev : Reversible μ Q := trace_chain_reversible π P hrev A hπ hA
  have hnonneg : 0 ≤ dirichlet μ Q f f := dirichlet_self_nonneg hQrev.stationary f
  have hv' : Var μ f ≤ (18 * (n : ℝ) ^ 4) * dirichlet μ Q f f := by
    apply hv.trans
    rw [← mul_assoc]
    exact mul_le_mul_of_nonneg_right hcoef hnonneg
  change (1 / (18 * (n : ℝ) ^ 4)) * Var μ f ≤ dirichlet μ Q f f
  rw [one_div, ← div_eq_inv_mul]
  exact (div_le_iff₀ (by positivity : 0 < 18 * (n : ℝ) ^ 4)).mpr (by simpa only [mul_comm] using hv')

end CountingMatroid.Analysis.TransversalTraceSpectralGap

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · applied the existing transversal variance theorem to the canonical harmonic extension and proved the concrete trace spectral gap 1/(18*n^4), including n=1.
-/
