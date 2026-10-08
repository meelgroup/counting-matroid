import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List
import CountingMatroid.Analysis.FirstPhaseFailure
import CountingMatroid.Analysis.InitialRestartLaw
import CountingMatroid.Analysis.BoundedRunResourceEnvelope
import CountingMatroid.Analysis.EmpiricalPhaseCertificate
import CountingMatroid.Analysis.PhaseMeanCertificate
import CountingMatroid.Analysis.TransversalClassPartition
import CountingMatroid.Analysis.TypeMassLowerBounds
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.IdealExchangeChain
import CountingMatroid.Analysis.ObservableProjection
import CountingMatroid.Analysis.ExchangeProposalGeometry
import CountingMatroid.Analysis.ObservablePoincare
import CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapePhaseControl

open CountingMatroid.Model

/-- INTERNAL: A completed run admits empirical phase ratios obeying the
paper's relative ratio bounds and multiplying to its actual output. A proof
from the program should take these ratios from the successive `finishPhase`
results, using the learned tables from the same execution.
TEXLINE: main.tex:1190-1205,1290-1304 -/
def AccurateRatioProduct (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
  ∃ R : ℕ → ℚ,
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
      (2 : ℚ) ^ n * (∏ j ∈ Finset.range s.L, R j) ∧
    ∀ j < s.L,
      (1 - s.η) / (1 + s.η) ≤ R j / (C (j + 1) / C j) ∧
      R j / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η)

/-- INTERNAL: A nonzero capped finite-tape run fails to admit accurate
empirical ratios with probability at most one eighth. The intended witness
is the sequence of `finishPhase` ratios in `Program.boundedRun`.
The deterministic certificate extraction and first-failure union bound are
proved here. `EmpiricalPhaseCertificate` separates the raw restart and
correlated-observation estimates from deterministic finishing and learned-table
preservation. Its scalar arithmetic and exact once-per-index finishing
are proved in `RelativeObservationBounds` and `FinishPhaseEmpiricalUpdate`.
`AnnealingPartitionDrift` proves the concrete schedule's state-weight and
class-partition bounds and ideal-multiplier drift. `DefectPartitionPositive`
proves defect-class nonemptiness against the executable classifier.
`StationaryMeanIdentities` proves the fixed state-weight mean identities using
`TransversalClassPartition`'s proved classifier reindexing.
`PhaseMeanCertificate` therefore removes type-mean identities,
positivity, and multiplier drift from the random event. `InitialMultipliersGood`
proves the executable defect-fiber count and ideal initialization.
`TypeMassLowerBounds` proves lower bounds for all type and numerator means.
`IdealExchangeChain` constructs the normalized law and symmetric exchange
proposal and proves its Metropolis kernel stationary, extending the target by
zero on invalid states. `ObservableProjection` proves the type indicators and
annealing numerator satisfy the required projection range conditions.
`ExchangeProposalGeometry` proves that, on n-element states, the ideal
uniform-label proposal is the paper's half-lazy occupied/unoccupied proposal,
and proves that rejection preserves half-laziness. `ObservablePoincare`
proves the symmetric-conductance energy identity and states the independent
same-paper observable variance estimate.
`FiniteTapeRawPhaseFailureBound` combines the existing conditional abort and
masked-observation-MSE bounds over prefix-free successful consumed histories.
This closes the local finite-tape failure estimate without importing the
lower-tail module. The imported analytic estimates retain their own proof
obligations; this file introduces no additional stochastic proof debt. `InitialRestartLaw`
retains the proved phase-zero fresh-prefix/suffix identity.
`FirstPhaseFailure` supplies the operational certificates and counting cover.
TEXLINE: main.tex:1207-1296,1392-1427 -/
theorem finite_tape_inaccurate_ratios (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s ≠ 0 ∧
      ¬ AccurateRatioProduct n r o₁ o₂ p
        (fun i => (bits[i]?).getD false)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  have certified_product (tape : ℕ → Bool)
      (hc : ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j) :
      AccurateRatioProduct n r o₁ o₂ p tape := by
    let weights := (CountingMatroid.Model.Operations.initialWeights n).val
    let initial : CountingMatroid.Program.AnnealingCursor n :=
      ⟨(CountingMatroid.Model.Operations.allocateLearnedWeights n s.L weights).val,
        weights, 1, 0⟩
    let phase := BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s
    let history := fun j => (Arlib.Computation.Charged.repeatFor phase j
      (some initial)).val
    have fold_value
        (f : Option (CountingMatroid.Program.AnnealingCursor n) → ℕ →
          Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
            CountingMatroid.Model.Operations.Cell
            (Option (CountingMatroid.Program.AnnealingCursor n)))
        (l : List ℕ) (b : Option (CountingMatroid.Program.AnnealingCursor n)) :
        (Arlib.Computation.Charged.foldl f l b).val =
          l.foldl (fun acc j => (f acc j).val) b := by
      induction l generalizing b with
      | nil => rfl
      | cons a l ih =>
          simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons]
            using ih (f b a).val
    have hsucc (j : ℕ) : history (j + 1) = (phase j (history j)).val := by
      simp only [history, Arlib.Computation.Charged.repeatFor, fold_value,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let R := fun j => if hj : j < s.L then Classical.choose (hc j hj) else 1
    have hR (j : ℕ) (hj : j < s.L) :
        (1 - s.η) / (1 + s.η) ≤
          R j / (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
            TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ∧
        R j / (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
            TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ≤
          (1 + s.η) / (1 - s.η) ∧
        ∃ current next : CountingMatroid.Program.AnnealingCursor n,
          history j = some current ∧
          (phase j (some current)).val = some next ∧
          next.product = current.product * R j ∧
          FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
          (j + 1 < s.L →
            FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s (j + 1) next) := by
      simpa only [R, dif_pos hj] using Classical.choose_spec (hc j hj)
    have hproduct : ∀ k ≤ s.L,
        ∃ result : CountingMatroid.Program.AnnealingCursor n,
          history k = some result ∧
            result.product = ∏ j ∈ Finset.range k, R j := by
      intro k
      induction k with
      | zero =>
          intro _
          exact ⟨initial, rfl, by simp [initial]⟩
      | succ k ih =>
          intro hk
          obtain ⟨previous, hprevious, hp⟩ := ih (by omega)
          obtain ⟨current, next, hcurrent, hnext, hmul, _⟩ :=
            (hR k (by omega)).2.2
          have heq : current = previous := Option.some.inj (hcurrent.symm.trans hprevious)
          subst current
          refine ⟨next, ?_, ?_⟩
          · rw [hsucc, hprevious]
            exact hnext
          · rw [hmul, hp, Finset.prod_range_succ]
    obtain ⟨result, hresult, hprod⟩ := hproduct s.L le_rfl
    have hout : CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
        (2 : ℚ) ^ n * result.product := by
      simp only [CountingMatroid.Interface.Pseudocode.singleRun,
        CountingMatroid.Program.boundedRun, Arlib.Computation.Charged.val_bind]
      change (match history s.L with
        | none => pure (0, 0)
        | some result =>
          (do
            let power ← CountingMatroid.Program.natPower 2 n
            let scale ← CountingMatroid.Model.Operations.ratOfNat power
            let estimate ← CountingMatroid.Model.Operations.ratMul scale result.product
            pure (estimate, result.bitCursor))).val.1 = _
      rw [hresult]
      simp only [Arlib.Computation.Charged.val_bind,
        BoundedRunResourceEnvelope.natPower_value,
        CountingMatroid.Model.Operations.ratOfNat,
        CountingMatroid.Model.Operations.ratMul,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      norm_cast
    refine ⟨R, ?_, ?_⟩
    · exact hout.trans (congrArg ((2 : ℚ) ^ n * ·) hprod)
    · intro j hj
      exact ⟨(hR j hj).1, (hR j hj).2.1⟩
  let bad := fun j => {bits : List Bool | bits.length = m ∧
    FirstPhaseFailure.FirstFailure r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  let inaccurate : Set (List Bool) := {bits | bits.length = m ∧
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
      (fun i => (bits[i]?).getD false) s ≠ 0 ∧
    ¬ AccurateRatioProduct n r o₁ o₂ p (fun i => (bits[i]?).getD false)}
  let uncertified : Set (List Bool) := {bits | bits.length = m ∧
    ¬ ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have hsubset : inaccurate ⊆ uncertified := by
    intro bits hb
    refine ⟨hb.1, ?_⟩
    intro hall
    exact hb.2.2 (certified_product _ hall)
  have hfinite : uncertified.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : inaccurate.ncard ≤ ∑ j ∈ Finset.range s.L, (bad j).ncard :=
    (Set.ncard_le_ncard hsubset hfinite).trans
      (FirstPhaseFailure.uncertified_card_le_sum n r o₁ o₂ s m)
  have hcast : (inaccurate.ncard : ENNReal) ≤
      ∑ j ∈ Finset.range s.L, ((bad j).ncard : ENNReal) := by
    exact_mod_cast hcard
  have hη : 0 ≤ s.η := by
    change 0 ≤ p.ε / ((32 * (s.L + 1) : ℕ) : ℚ)
    exact div_nonneg p.ε_pos.le (Nat.cast_nonneg _)
  have hηsmall : s.η ≤ (1 / 3 : ℚ) := by
    have hformula : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
      change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
      push_cast
      rfl
    rw [hformula]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 32 * ((s.L : ℚ) + 1))).mpr
    have hL : (0 : ℚ) ≤ s.L := Nat.cast_nonneg _
    linarith [p.ε_lt_one]
  let rawBad := fun j => {bits : List Bool | bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have initial_good : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s 0
      (BoundedRunPhaseHistory.initialCursor n s) := by
    simp [FirstPhaseFailure.GoodStoredMultipliers,
      BoundedRunPhaseHistory.initialCursor,
      CountingMatroid.Model.Operations.initialWeights,
      CountingMatroid.Model.Operations.allocateLearnedWeights,
      InitialMultipliersGood.initial_ideal_multiplier]
  have history_good (tape : ℕ → Bool) (j : ℕ) (hj : j < s.L)
      (hprevious : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s a) :
      ∃ current : CountingMatroid.Program.AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
        FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current := by
    cases j with
    | zero => exact ⟨BoundedRunPhaseHistory.initialCursor n s, rfl, initial_good⟩
    | succ j =>
      obtain ⟨ratio, _, _, current, next, hcurrent, hnext, _, _, hgood⟩ :=
        hprevious j (Nat.lt_succ_self j)
      refine ⟨next, ?_, hgood hj⟩
      rw [BoundedRunPhaseHistory.phaseHistory_succ,
        show BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current
          from hcurrent]
      exact hnext
  have hq (j : ℕ) : 0 < s.ρ ^ j :=
    pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
  let controlledBad := fun j => {bits : List Bool | bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ∃ current : CountingMatroid.Program.AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
      ∃ hw : ∀ index, 0 < current.currentWeights index,
      Arlib.Probability.Stationary
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn (hq j) hw) ∧
      (∀ state : PairedSet n, state.card = n →
        (1 / 2 : ℝ) ≤ IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn (hq j) hw state state) ∧
      (∀ state : PairedSet n, state.card = n → ∀ F : PairedSet n → ℝ,
        (∑ next : PairedSet n,
          IdealExchangeChain.exchangeProposal n hn state next * F next) =
          (1 / 2 : ℝ) * F state + (1 / (2 * (n : ℝ) ^ 2)) *
            ∑ a ∈ state, ∑ b ∈ stateᶜ, F (insert b (state.erase a))) ∧
      (∀ kind state,
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw) state *
          ObservableProjection.observableProjection
            (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
              current.currentWeights (hq j) hw)
            (IdealExchangeChain.typeIndicator kind) state =
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw) state *
          IdealExchangeChain.typeIndicator kind state) ∧
      (ObservableProjection.observableProjection
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.numeratorObservable r o₁ o₂ s.ρ) =
        IdealExchangeChain.numeratorObservable r o₁ o₂ s.ρ) ∧
      (1 / (5 * (n : ℝ) ^ 2) ≤ Arlib.Probability.FinDist.Ex
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.typeIndicator .transversal)) ∧
      (1 / (20 * (n : ℝ) ^ 2) ≤ Arlib.Probability.FinDist.Ex
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.numeratorObservable r o₁ o₂ s.ρ)) ∧
      (∀ index : DefectIndex n, 1 / (20 * (n : ℝ) ^ 2) ≤ Arlib.Probability.FinDist.Ex
        (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights (hq j) hw)
        (IdealExchangeChain.typeIndicator (.defect index.emptyPair index.fullPair))) ∧
      (∀ H : PairedSet n → ℝ,
        Arlib.Probability.FinDist.Var
          (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
            current.currentWeights (hq j) hw)
          (ObservableProjection.observableProjection
            (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
              current.currentWeights (hq j) hw) H) ≤
          2000 * (n : ℝ) ^ 6 * Arlib.MarkovChains.dirichlet
            (IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
              current.currentWeights (hq j) hw)
            (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
              current.currentWeights hn (hq j) hw) H H) ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => (bits[i]?).getD false) s j}
  have hrawlocal (j : ℕ) (hj : j ∈ Finset.range s.L) :
      ((rawBad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        1 / (8 * ((s.L : ENNReal) + 1)) := by
    have hsubsetControlled : rawBad j ⊆ controlledBad j := by
      intro bits hb
      obtain ⟨current, hcurrent, hgood⟩ :=
        history_good _ j (Finset.mem_range.mp hj) hb.2.1
      obtain ⟨_, hzero, hdefects⟩ := TypeMassLowerBounds.good_type_mass_bounds
        r o₁ o₂ (s.ρ ^ j) current.currentWeights hn
        (pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j)
        hgood.2
      have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j) :=
        (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
      have hw (index : DefectIndex n) : 0 < current.currentWeights index :=
        (div_pos (div_pos hC
          (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (s.ρ ^ j)
            (hq j) index)) (by norm_num : (0 : ℚ) < 4)).trans_le
          (hgood.2 index).1
      refine ⟨hb.1, hb.2.1, current, hcurrent, hgood, hw,
        IdealExchangeChain.ideal_chain_stationary r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hn (hq j) hw,
        (fun state hcard => ExchangeProposalGeometry.ideal_chain_lazy r o₁ o₂
          (s.ρ ^ j) current.currentWeights hn (hq j) hw state hcard),
        (fun state hcard F => ExchangeProposalGeometry.exchange_proposal_average
          n hn state hcard F),
        (fun kind state => ObservableProjection.type_indicator_projected
          r o₁ o₂ (s.ρ ^ j) current.currentWeights (hq j) hw kind state),
        ObservableProjection.numerator_observable_projected r o₁ o₂ s.ρ _,
        ?_, ?_, ?_, ?_, hb.2.2⟩
      · rw [IdealExchangeChain.operational_type_mean]
        have hr := (Rat.cast_le (K := ℝ)).mpr hzero
        push_cast at hr
        exact hr
      · rw [IdealExchangeChain.operational_numerator_mean]
        have hu := TypeMassLowerBounds.good_numerator_mean_lower_bound
          n r o₁ o₂ p j current.currentWeights hn hgood.2
        have hr := (Rat.cast_le (K := ℝ)).mpr hu
        push_cast at hr
        exact hr
      · intro index
        rw [IdealExchangeChain.operational_type_mean]
        have hr := (Rat.cast_le (K := ℝ)).mpr (hdefects index)
        push_cast at hr
        exact hr
      · intro H
        have hqone : s.ρ ^ j ≤ 1 := by
          calc
            s.ρ ^ j ≤ (1 : ℚ) ^ j := pow_le_pow_left₀
              (AnnealingPartitionDrift.schedule_power_lower n p hn).1.le
              (AnnealingPartitionDrift.schedule_power_lower n p hn).2.1 j
            _ = 1 := by simp
        exact ObservablePoincare.observable_poincare n r M₁ M₂ o₁ o₂
          (s.ρ ^ j) current.currentWeights hn hfull hr h₁ h₂
          (hq j) hqone hw hgood.2 H
    have hcontrolled : ((controlledBad j).ncard : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤ 1 / (8 * ((s.L : ENNReal) + 1)) := by
      have hsubsetRaw : controlledBad j ⊆ rawBad j := by
        intro bits hb
        rcases hb with ⟨hlen, hprevious, current, hcurrent, hgood, hw,
          hstationary, hlazy, hproposal, htypeProjection, hnumeratorProjection,
          hzeroMean, hnumeratorMean, hdefectMeans, hpoincare, hraw⟩
        exact ⟨hlen, hprevious, hraw⟩
      have hfiniteRaw : (rawBad j).Finite :=
        (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
      have hc : ((controlledBad j).ncard : ENNReal) ≤
          ((rawBad j).ncard : ENNReal) := by
        exact_mod_cast Set.ncard_le_ncard hsubsetRaw hfiniteRaw
      exact (mul_le_mul_of_nonneg_right hc bot_le).trans
        (FiniteTapeRawPhaseFailureBound.finite_tape_raw_phase_failure_bound
          n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j
          (Finset.mem_range.mp hj))
    have hfiniteControlled : (controlledBad j).Finite :=
      (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
    have hc : ((rawBad j).ncard : ENNReal) ≤ ((controlledBad j).ncard : ENNReal) := by
      exact_mod_cast Set.ncard_le_ncard hsubsetControlled hfiniteControlled
    exact (mul_le_mul_of_nonneg_right hc bot_le).trans hcontrolled
  have hlocal (j : ℕ) (hj : j ∈ Finset.range s.L) :
      ((bad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        1 / (8 * ((s.L : ENNReal) + 1)) := by
    have hsubsetRaw : bad j ⊆ rawBad j := by
      intro bits hb
      refine ⟨hb.1, hb.2.1, ?_⟩
      intro hraw
      exact hb.2.2 (EmpiricalPhaseCertificate.raw_phase_certified
        r o₁ o₂ _ s j hη hηsmall
        (PhaseMeanCertificate.raw_phase_means_estimates n r o₁ o₂ p hn _ j hraw))
    have hfiniteRaw : (rawBad j).Finite :=
      (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
    have hc : ((bad j).ncard : ENNReal) ≤ ((rawBad j).ncard : ENNReal) := by
      exact_mod_cast Set.ncard_le_ncard hsubsetRaw hfiniteRaw
    exact (mul_le_mul_of_nonneg_right hc bot_le).trans (hrawlocal j hj)
  change (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤ _
  calc
    (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        (∑ j ∈ Finset.range s.L, ((bad j).ncard : ENNReal)) *
          (1 / 2 : ENNReal) ^ m := mul_le_mul_of_nonneg_right hcast bot_le
    _ = ∑ j ∈ Finset.range s.L,
        ((bad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := Finset.sum_mul ..
    _ ≤ ∑ _j ∈ Finset.range s.L, 1 / (8 * ((s.L : ENNReal) + 1)) :=
      Finset.sum_le_sum hlocal
    _ = (s.L : ENNReal) * (1 / (8 * ((s.L : ENNReal) + 1))) := by simp
    _ = (1 / 8 : ENNReal) * ((s.L : ENNReal) / ((s.L : ENNReal) + 1)) := by
      simp only [div_eq_mul_inv, one_mul,
        ENNReal.mul_inv (Or.inl (by norm_num : (8 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (8 : ENNReal) ≠ ⊤))]
      ac_rfl
    _ ≤ (1 / 8 : ENNReal) * 1 :=
      mul_le_mul_of_nonneg_left (ENNReal.div_le_of_le_mul (by simp)) bot_le
    _ = (1 / 8 : ENNReal) := mul_one _

end CountingMatroid.Analysis.FiniteTapePhaseControl

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · publication blocked · the helper's granted build and the parent's standalone elaboration passed without local sorry warnings. After concurrent dependency updates, the final parent check cannot load ConditionalObservationAbortMass.olean. A later publication build was interrupted while recompiling live-owned dependency files; their owners must publish their artifacts. No source proof was discarded and no new mathematical obligation was introduced.

* r25 · assembled · closed the local raw-mean finite-tape bound through a proved prefix-free counting helper, using the existing conditional abort and observation-MSE declarations. The assigned theorem has no local sorry; imported quantitative analytic obligations remain in their owning modules.

* r23 · decomposed · proved the exact n-element proposal average, half-laziness, and the zero-weight-safe Metropolis energy identity. The parent semantically uses proposal averaging and laziness and the separately stated same-paper observable Poincare estimate. Its weighted transport proof and the parent's conditional finite-tape failure bound remain open; a live handoff is being requested.

* r22 · proved support · proved exact initial defect partition counts and ideal multipliers, reached-good-history cover, all observable mean lower bounds, a concrete symmetric exchange proposal and stationary Metropolis law, and observable projection range conditions. Both live handoffs were mechanically rejected without specific diagnostics; initialization was proved locally and the provisional Poincare obligation was removed. The sole remaining proof gap is the local conditional first-failure probability bound, with no new exported proof debt.

* r21 · proved support · mechanical handoff r21-transversal-reindex-1 was rejected without further diagnostic, so the classifier characterization and transversal reindexing were proved locally. All new children are proved; the only proof gap remains the local conditional finite-tape empirical-mean failure bound.

* r21 · decomposed · normalized actual state weights fix every observable mean; the bridge now proves mean and multiplier identities from the independent transversal-class reindexing child. Its sum_bij proof closes injectivity and weight agreement and exposes the executable classifier's forward/reverse scan invariant. Defect-class positivity is proved independently.

* r21 · proved support · proved schedule cooling bounds, operational class-partition bounds, and ideal-multiplier drift. PhaseMeanCertificate removes true-ratio positivity and drift from the sole remaining stochastic mean-failure event; exact type-mean identities, conditional restart/MSE, and finite-tape coupling remain open locally.

* recovery · proved support · closed the exact once-per-index finishing lemma after rejected handoff. The new raw-estimate-to-certified-phase implication has no unproved children; the stochastic raw-estimate bound is the only remaining local gap.

* recovery · decomposed · replaced final-output certificate failure by raw empirical mean/restart failure; proved scalar ratio and learned-weight bounds and deterministic table preservation. Exact once-per-index finishing is isolated in FinishPhaseEmpiricalUpdate; the stochastic raw-estimate bound remains local. The assigned theorem statement and all existing imports are preserved.

* r19 · partial · proved and used the exact fresh-prefix/observation-suffix law for phase zero; the base observation concentration and positive-phase conditional restart/MSE estimates remain local to this theorem. All new support declarations are proved.

* r18 · partial · handoff mechanically rejected; retained all checked deterministic progress, proved the first-failure counting cover upstream, and kept the missing per-phase conditional probability estimate inside the assigned theorem. No new exported unproved helper remains.

* r18 · decomposed · checked deterministic extraction from actual charged phase prefixes and the finite union bound; the remaining conditional first-phase failure estimate is isolated and semantically used from `FirstPhaseFailure.finite_tape_first_phase_failure`.

* 2026-10-08 · blocked · fresh stdin probes with `exact?` and unfolding plus `aesop` leave the phase-fold event bound. Verified the pretest-cost dependency is irrelevant, the warm-start MSE/trace estimates remain missing, and the proved fair-tape counting conversion is downstream. No new declarations or proof debt.
* r16 · blocked · live handoff admission was mechanically rejected with no further diagnostic; ownership remains here. Both unfolding with `aesop` and direct `exact?` failed on the missing phase probability bound.
* r16 · open · extracted the accurate-ratio witness probability bound; unfolding the actual bounded-run fold and `aesop` leave the conditional phase law and finite-tape coupling. The deterministic product implication is proved separately.
-/
