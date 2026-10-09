import CountingMatroid.Analysis.PositiveTimeTraceMixing
import CountingMatroid.Analysis.AnnealingPartitionDrift

set_option autoImplicit false

/-!
The schedule supplies pointwise factor-two domination for the concrete
uncapped positive-time transversal trace, from every transversal start.
This is an analytical estimate; it does not identify the finite-tape restart law.
-/
namespace CountingMatroid.Analysis.ScheduledTransversalTraceMixing

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.StationaryMeanIdentities
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.TransversalTraceSpectralGap
open CountingMatroid.Analysis.PositiveTimeTraceChain
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Evaluate a transversal weight independently of its multipliers.
TEXLINE: main.tex:721-728 -/
private theorem transversal_weight {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (x : PairedSet n)
    (hx : x ∈ transversalSet n) :
    stateWeight r o₁ o₂ q w x =
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ x).val) := by
  have hk : (classifyState x).val = .transversal := by
    simpa only [transversalSet, Finset.mem_filter, Finset.mem_univ, true_and] using hx
  simp [stateWeight, hk, weightOfKind, CountingMatroid.Model.Operations.natSub,
    BoundedRunResourceEnvelope.ratPower_value]

/-- INTERNAL: The conditional trace law is the transversal weight divided
by its partition sum, and is independent of the defect multipliers.
TEXLINE: main.tex:1023-1037,1215-1218 -/
private theorem trace_law_formula {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ a, 0 < w a) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let A := transversalSet n
    (∑ x ∈ A, π x) = (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) /
      (normalizer r o₁ o₂ q w : ℝ) := by
  classical
  dsimp only
  have hid := (stationary_mean_identities r o₁ o₂ q 1 w hq hw).2.1
  have hc := congrArg (fun a : ℚ => (a : ℝ)) hid
  simp only [typeMean, Rat.cast_div, Rat.cast_sum, apply_ite, Rat.cast_zero] at hc
  simpa only [transversalSet, Finset.sum_filter, operationalLaw, ite_div, zero_div,
    Finset.sum_div] using hc

/-- INTERNAL: The explicit trace length suppresses the spectral contraction
below the paper's uniform lower mass bound.
TEXLINE: main.tex:1215-1223 -/
private theorem schedule_trace_decay (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    (1 - 1 / (18 * (n : ℝ) ^ 4)) ^ s.τ ≤ (1 / 2 : ℝ) ^ (n * (s.L + 1)) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let b := 18 * n ^ 4
  let N := n * (s.L + 1)
  have hb : 0 < b := by dsimp [b]; positivity
  have hbr : (b : ℝ) = 18 * (n : ℝ) ^ 4 := by simp [b]
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  have hbase0 : 0 ≤ 1 - 1 / (b : ℝ) := by
    have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hb1
    exact sub_nonneg.mpr (by simpa only [div_one] using this)
  have hbase1 : 1 - 1 / (b : ℝ) ≤ 1 := sub_le_self _ (by positivity)
  have hblock : (1 - 1 / (b : ℝ)) ^ b ≤ (1 / 2 : ℝ) :=
    (Real.one_sub_div_pow_le_exp_neg (n := b) (t := 1) hb1).trans
      Real.exp_neg_one_lt_half.le
  have hτ : s.τ = 20 * n ^ 4 * (N + 2) := by rfl
  have hlength : b * N ≤ s.τ := by
    rw [hτ]
    dsimp [b]
    nlinarith
  calc
    _ = (1 - 1 / (b : ℝ)) ^ s.τ := by rw [hbr]
    _ ≤ (1 - 1 / (b : ℝ)) ^ (b * N) :=
      pow_le_pow_of_le_one hbase0 hbase1 hlength
    _ = ((1 - 1 / (b : ℝ)) ^ b) ^ N := pow_mul _ _ _
    _ ≤ (1 / 2 : ℝ) ^ N := pow_le_pow_left₀ (pow_nonneg hbase0 _) hblock _

/-- PAPER: main.tex:1215-1223,1242-1244
After the scheduled number of positive-time trace transitions, every starting
transversal has endpoint density at most twice the current transversal law. -/
theorem scheduled_transversal_trace_mixing (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (w : Multipliers n) (hn : 0 < n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hw : ∀ a, 0 < w a)
    (hgood : ∀ a,
      (TransversalPartition.partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) /
        FirstPhaseFailure.defectPartition r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) a) / 4 ≤ w a ∧
      w a ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) /
        FirstPhaseFailure.defectPartition r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ j) a))
    (x y : PairedSet n) (hx : x ∈ transversalSet n) (hy : y ∈ transversalSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    let P := idealChain r o₁ o₂ (s.ρ ^ j) w hn hq hw
    (PositiveTimeTraceKernel.iterate
      (PositiveTimeTraceKernel.uncappedReturn P (transversalSet n)) s.τ).entry x y ≤
      2 * ((((s.ρ ^ j) ^
        (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ y).val) : ℚ) : ℝ) /
        (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j) : ℝ)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hρ := AnnealingPartitionDrift.schedule_power_lower n p hn
  have hq : 0 < s.ρ ^ j := pow_pos hρ.1 j
  have hq1 : s.ρ ^ j ≤ 1 := pow_le_one₀ hρ.1.le hρ.2.1
  let q := s.ρ ^ j
  let π := operationalLaw r o₁ o₂ q w hq hw
  let P := idealChain r o₁ o₂ q w hn hq hw
  let A := transversalSet n
  have hCq : 0 < TransversalPartition.partitionSum r o₁ o₂ q :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
  have hC : (0 : ℝ) < (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) := by
    exact_mod_cast hCq
  have hZ : (0 : ℝ) < (normalizer r o₁ o₂ q w : ℝ) := by
    exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 w hq hw).1
  have hπ : ∀ z ∈ A, 0 < π z := by
    intro z hz
    change 0 < (stateWeight r o₁ o₂ q w z : ℝ) / _
    rw [transversal_weight r o₁ o₂ q w z hz]
    exact div_pos (by exact_mod_cast pow_pos hq _) hZ
  have hA : 0 < ∑ z ∈ A, π z := by
    rw [trace_law_formula r o₁ o₂ q w hq hw]
    exact div_pos hC hZ
  let μ := traceLaw π A hA
  let Q := traceChain π P (ideal_chain_stationary r o₁ o₂ q w hn hq hw) A hπ
  have hμ (z : A) : μ z =
      ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val) : ℚ) : ℝ) /
      (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) := by
    change (π z / (∑ z ∈ A, π z)) = _
    rw [trace_law_formula r o₁ o₂ q w hq hw]
    change ((stateWeight r o₁ o₂ q w z : ℝ) / _) / _ = _
    rw [transversal_weight r o₁ o₂ q w z z.property]
    field_simp
  let N := n * (s.L + 1)
  let m := (1 / 2 : ℝ) ^ N
  have hm : 0 < m := by dsimp [m]; positivity
  have hmin : ∀ z : A, m ≤ μ z := by
    intro z
    rw [hμ]
    have hCupper : (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) ≤ (2 : ℝ) ^ n := by
      have hcq : TransversalPartition.partitionSum r o₁ o₂ q ≤ (2 : ℚ) ^ n := by
        calc
          _ ≤ ∑ _z : Finset (Fin n), (1 : ℚ) :=
            Finset.sum_le_sum fun z _ => pow_le_one₀ hq.le hq1
          _ = _ := by simp
      exact_mod_cast hcq
    have hWlower : (1 / 2 : ℝ) ^ j ≤
        ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val) : ℚ) : ℝ) := by
      have hpow : (1 / 2 : ℚ) ^ j ≤ q ^ n := by
        change (1 / 2 : ℚ) ^ j ≤ (s.ρ ^ j) ^ n
        rw [← pow_mul, Nat.mul_comm j n, pow_mul]
        exact pow_le_pow_left₀ (by norm_num) hρ.2.2 j
      have hd : n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val ≤ n :=
        Nat.sub_le _ _
      have hfinal := hpow.trans (pow_le_pow_of_le_one hq.le hq1 hd)
      change (1 / 2 : ℝ) ^ j ≤
        (((s.ρ ^ j) ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ z).val) : ℚ) : ℝ)
      have hh := (Rat.cast_le (K := ℝ)).mpr hfinal
      norm_num only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
      simpa only [Rat.cast_pow] using hh
    have hNj : n + j ≤ N := by
      have hmL := Nat.le_mul_of_pos_left s.L hn
      dsimp [N]
      nlinarith
    calc
      m ≤ (1 / 2 : ℝ) ^ (n + j) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) hNj
      _ = (1 / 2 : ℝ) ^ j / (2 : ℝ) ^ n := by
        rw [pow_add, div_pow, one_pow]
        ring
      _ ≤ _ := div_le_div₀ (by positivity) hWlower hC hCupper
  have hrev : Reversible π P := metropolis_reversible_zero_weights π
    (exchangeProposal n hn) (exchange_proposal_symmetric n hn)
  have hQrev : Reversible μ Q := trace_chain_reversible π P hrev A hπ hA
  have hholding : ∀ z, (1 / 2 : ℝ) ≤ P z z := by
    intro z
    have hlazy := IdealChainNonnegDefinite.exchange_proposal_holding n hn z
    have hsum : exchangeProposal n hn z z +
        ∑ v ∈ Finset.univ.erase z, exchangeProposal n hn z v = 1 := by
      rw [Finset.add_sum_erase _ _ (Finset.mem_univ z)]
      exact (exchangeProposal n hn).sum_coe z
    have hle : (∑ v ∈ Finset.univ.erase z, mhRate π (exchangeProposal n hn) z v) ≤
        ∑ v ∈ Finset.univ.erase z, exchangeProposal n hn z v :=
      Finset.sum_le_sum fun v _ => mhRate_le_proposal π (exchangeProposal n hn) z v
    change (1 / 2 : ℝ) ≤ metropolis π (exchangeProposal n hn) z z
    rw [metropolis_apply_self, mhStay]
    linarith
  have hpsd : NonnegDefinite μ Q := IdealChainNonnegDefinite.nonnegDefinite_of_holding
    μ Q hQrev.stationary (trace_chain_holding π P hrev.stationary A hπ hholding)
  have hgap := transversal_trace_spectral_gap n r M₁ M₂ o₁ o₂ q w hn
    hfull hr h₁ h₂ hq hq1 hw hgood hπ hA
  have hnreal : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hγ : 1 / (18 * (n : ℝ) ^ 4) ≤ 1 := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 18 * (n : ℝ) ^ 4)).mpr
    have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hnreal 4
    norm_num at this
    linarith
  have hmix := PositiveTimeTraceMixing.pointwise_mixing_le_of_gap μ Q hQrev hpsd
    (1 / (18 * (n : ℝ) ^ 4)) m hgap hγ hm hmin s.τ
    (schedule_trace_decay n p hn) ⟨x, hx⟩ ⟨y, hy⟩
  rw [trace_chain_iter π P hrev.stationary A hπ, hμ] at hmix
  exact hmix

end CountingMatroid.Analysis.ScheduledTransversalTraceMixing

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · normalized the concrete boundary law, bounded every transversal mass below by 2^(-n*(L+1)), and applied spectral contraction at the actual scheduled trace length. No finite-tape coupling is assumed.
-/
