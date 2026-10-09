import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.RestartPhaseTransversal
import CountingMatroid.Analysis.PositiveTimeTraceKernel
import CountingMatroid.Analysis.ScheduledTransversalTraceMixing
import CountingMatroid.Analysis.RestartSuffixMassDefinition
import CountingMatroid.Analysis.CappedRestartFinalTraceDomination

set_option autoImplicit false

/-!
The finite-suffix restart endpoint sublaw needed for recorded-path domination.
Successful restarts contribute their returned state; aborted restarts contribute
zero. The stationary-law comparison and phase-zero finite-tape bound are
proved. A separate module constructs capped and uncapped positive-time return
subkernels and proves their monotone comparison. The remaining positive-phase
obligation is the finite-suffix coupling. The concrete trace spectral estimate
and its scheduled pointwise factor-two mixing bound are proved in imported modules.
-/
namespace CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: Convert a factor-two transversal endpoint bound to the
paper's enlarged-chain domination factor, using its existing type-mass bound.
TEXLINE: main.tex:1242-1246 -/
theorem warm_endpoint_operational_comparison {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index))
    (mass : ℝ) (state : PairedSet n)
    (hwarm : mass ≤ 2 * ((stateWeight r o₁ o₂ q w state : ℝ) /
      (TransversalPartition.partitionSum r o₁ o₂ q : ℝ))) :
    mass ≤ (10 * (n : ℝ) ^ 2) *
      IdealExchangeChain.operationalLaw r o₁ o₂ q w hq hw state := by
  have hCq : 0 < TransversalPartition.partitionSum r o₁ o₂ q := by
    apply Finset.sum_pos
    · intro A _
      exact pow_pos hq _
    · exact Finset.univ_nonempty
  have hC : (0 : ℝ) < (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) :=
    by exact_mod_cast hCq
  have hZ : (0 : ℝ) < (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) := by
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
      r o₁ o₂ q 1 w hq hw).1
  have hW : (0 : ℝ) ≤ (stateWeight r o₁ o₂ q w state : ℝ) := by
    exact_mod_cast IdealExchangeChain.state_weight_nonneg r o₁ o₂ q w hq hw state
  have hbound : (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) ≤
      5 * (n : ℝ) ^ 2 * (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) := by
    exact_mod_cast (TypeMassLowerBounds.good_type_mass_bounds r o₁ o₂ q w hn hq hgood).1
  apply hwarm.trans
  change 2 * ((stateWeight r o₁ o₂ q w state : ℝ) / _) ≤
    (10 * (n : ℝ) ^ 2) * ((stateWeight r o₁ o₂ q w state : ℝ) / _)
  rw [← mul_div_assoc, ← mul_div_assoc]
  apply (div_le_div_iff₀ hC hZ).mpr
  nlinarith [mul_le_mul_of_nonneg_right hbound hW]

/-- INTERNAL: A phase-zero restart on a covered fresh finite suffix gives
each paired set mass at most the uniform transversal mass.
TEXLINE: main.tex:1163-1176,1242-1244 -/
theorem fresh_restart_suffix_mass_le (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (current : AnnealingCursor n) (hc : current.bitCursor = 0)
    (t : ℕ) (ht : n ≤ t) (state : PairedSet n) :
    restartSuffixMass r o₁ o₂ s 0 current [] t state ≤ 1 / (2 : ℝ) ^ n := by
  classical
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le ht
  let fresh := fun bits : Fin n → Bool =>
    Finset.univ.image (fun i : Fin n => (i, bits i))
  have hfresh : Function.Injective fresh := by
    intro bits bits' heq
    funext i
    have hi : (i, bits i) ∈ fresh bits' := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    symm
    simpa only [fresh, Finset.mem_image, Finset.mem_univ, true_and,
      Prod.mk.injEq, exists_eq_left] using hi
  let e : ((Fin n → Bool) × (Fin k → Bool)) ≃ List.Vector Bool (n + k) :=
    (Fin.appendEquiv n k).trans (Equiv.vectorEquivFin Bool (n + k)).symm
  unfold restartSuffixMass
  simp only [hc, InitialRestartLaw.restartPhase_zero, List.nil_append,
    zero_add, Option.map_some, Option.some.injEq]
  rw [← e.sum_comp, Fintype.sum_prod_type]
  have hfirst (bits : Fin n → Bool) (rest : Fin k → Bool) (i : Fin n) :
      (((e (bits, rest)).val)[i.val]?).getD false = bits i := by
    change ((List.Vector.ofFn (Fin.append bits rest)).toList[i.val]?).getD false = bits i
    rw [List.Vector.toList_ofFn]
    rw [List.getElem?_ofFn, dif_pos (by omega)]
    change Fin.append bits rest (Fin.castAdd k i) = bits i
    simp
  have hterm (bits : Fin n → Bool) (rest : Fin k → Bool) :
      (Finset.univ.image (fun i : Fin n =>
        (i, (((e (bits, rest)).val)[i.val]?).getD false))) = fresh bits := by
    apply Finset.image_congr
    intro i _
    exact congrArg (Prod.mk i) (hfirst bits rest i)
  simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, nsmul_eq_mul]
  by_cases hex : ∃ bits : Fin n → Bool, fresh bits = state
  · obtain ⟨bits, hb⟩ := hex
    have hevent (bits' : Fin n → Bool) : fresh bits' = state ↔ bits' = bits := by
      rw [← hb]
      exact hfresh.eq_iff
    simp only [hevent]
    rw [Finset.sum_eq_single bits]
    · simp only [if_true]
      rw [pow_add, Nat.cast_pow, Nat.cast_ofNat]
      exact le_of_eq (by field_simp)
    · intro bits' _ hne
      simp [hne]
    · simp
  · have hnone (bits : Fin n → Bool) : fresh bits ≠ state := by
      intro hb
      exact hex ⟨bits, hb⟩
    simp only [hnone, if_false, mul_zero, Finset.sum_const_zero]
    positivity

/-- INTERNAL: Transfer the paper's uncapped warm restart endpoint bound to
the actual capped finite-suffix sublaw. This excludes aborts, without
renormalising the successful restart distribution.
TEXLINE: main.tex:1207-1244,1392-1421 -/
theorem successful_prefix_restart_endpoint_mass_domination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (hfixed : ∀ suffix : List.Vector Bool
        (CountingMatroid.Model.Run.blockLength n r p - pref.length),
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) j = some current)
    (state : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    restartSuffixMass r o₁ o₂ s j current pref t state ≤
      (10 * (n : ℝ) ^ 2) *
        IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hq hw state := by
  classical
  dsimp only
  by_cases hinvalid : (classifyState state).val ≠ .transversal
  · have hzero : restartSuffixMass r o₁ o₂
        (CountingMatroid.Interface.Pseudocode.setup n p) j current pref
        (CountingMatroid.Model.Run.blockLength n r p - pref.length) state = 0 := by
      unfold restartSuffixMass
      apply Finset.sum_eq_zero
      intro suffix _
      apply if_neg
      intro hstate
      obtain ⟨start, hstart, heq⟩ := Option.map_eq_some_iff.mp hstate
      change start.1 = state at heq
      exact hinvalid (heq ▸ RestartPhaseTransversal.restartPhase_transversal
        r o₁ o₂ _ _ _ _ _ start hstart)
    rw [hzero]
    exact mul_nonneg (by positivity) (Arlib.Probability.FinDist.coe_nonneg _ _)
  · have htrans : (classifyState state).val = .transversal := not_ne_iff.mp hinvalid
    apply warm_endpoint_operational_comparison r o₁ o₂ _ current.currentWeights
      hn _ hw hgood.2
    by_cases hjzero : j = 0
    · subst j
      have hpref : pref = [] := by
        obtain ⟨bits, _, _, hpref⟩ := hprefix
        change pref = bits.take 0 at hpref
        simpa only [List.take_zero] using hpref
      subst pref
      have hhistory := hfixed ⟨List.replicate
        (CountingMatroid.Model.Run.blockLength n r p - ([] : List Bool).length) false, by simp⟩
      change some (BoundedRunPhaseHistory.initialCursor n
        (CountingMatroid.Interface.Pseudocode.setup n p)) = some current at hhistory
      have hc : current.bitCursor = 0 := by
        rw [← Option.some.inj hhistory]
        rfl
      have hL : 0 < (CountingMatroid.Interface.Pseudocode.setup n p).L := hj
      have ht : n ≤ CountingMatroid.Model.Run.blockLength n r p := by
        have hmul := Nat.le_mul_of_pos_right n hL
        dsimp only [CountingMatroid.Interface.Pseudocode.setup] at hmul
        unfold CountingMatroid.Model.Run.blockLength
        dsimp only
        exact hmul.trans (by omega)
      have hfresh := fresh_restart_suffix_mass_le n r o₁ o₂
        (CountingMatroid.Interface.Pseudocode.setup n p) current hc
        (CountingMatroid.Model.Run.blockLength n r p) ht state
      have hW : stateWeight r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ 0)
          current.currentWeights state = 1 := by
        simp [stateWeight, htrans, weightOfKind, CountingMatroid.Model.Operations.natSub,
          BoundedRunResourceEnvelope.ratPower_value]
      have hC : TransversalPartition.partitionSum r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ 0) = (2 : ℚ) ^ n := by
        simp [TransversalPartition.partitionSum]
      simp only [List.length_nil, Nat.sub_zero, hW, hC, Rat.cast_one,
        Rat.cast_pow, Rat.cast_ofNat]
      exact hfresh.trans (by
        have hnonneg : 0 ≤ 1 / (2 : ℝ) ^ n := by positivity
        linarith)
    · let s := CountingMatroid.Interface.Pseudocode.setup n p
      have hq : 0 < s.ρ ^ j :=
        pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
      have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j) :=
        (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn j).1
      have htable : ∀ index, 0 < current.tables j index := by
        intro index
        exact (div_pos (div_pos hC
          (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (s.ρ ^ j) hq index))
          (by norm_num : (0 : ℚ) < 4)).trans_le (hgood.1 j le_rfl index).1
      let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ j)
        (current.tables j) hn hq htable
      let A : Finset (PairedSet n) :=
        Finset.univ.filter (fun x => (classifyState x).val = .transversal)
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      let ν := restartSuffixMass r o₁ o₂ s (j - 1) current pref t
      let bound := 2 * ((stateWeight r o₁ o₂ (s.ρ ^ j)
        current.currentWeights state : ℝ) /
        (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j) : ℝ))
      obtain ⟨hν, hνmass, hνsupport⟩ := restart_suffix_mass_subprobability
        r o₁ o₂ s (j - 1) current pref t
      have hbound : 0 ≤ bound := by
        apply mul_nonneg (by norm_num)
        apply div_nonneg
        · exact_mod_cast IdealExchangeChain.state_weight_nonneg r o₁ o₂
            (s.ρ ^ j) current.currentWeights hq hw state
        · exact_mod_cast hC.le
      suffices htrace :
          restartSuffixMass r o₁ o₂ s j current pref t state ≤
            ∑ x, ν x * (PositiveTimeTraceKernel.iterate
              (PositiveTimeTraceKernel.returnWithin P A s.restartCap) s.τ).entry x state ∧
          ∀ x ∈ A, (PositiveTimeTraceKernel.iterate
            (PositiveTimeTraceKernel.uncappedReturn P A) s.τ).entry x state ≤ bound by
        exact PositiveTimeTraceKernel.endpoint_mass_le_of_capped_trace P A
          s.restartCap s.τ ν hν hνmass
          (fun x hx => hνsupport x (by simpa only [A, Finset.mem_filter,
            Finset.mem_univ, true_and] using hx)) _ bound hbound state htrace.1 htrace.2
      refine ⟨?_, ?_⟩
      · exact CappedRestartFinalTraceDomination.capped_restart_final_trace_domination
          n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj
          (Nat.pos_of_ne_zero hjzero) pref hprefix current hw hgood htable hfixed state
      · intro x hx
        have hxA : x ∈ TransversalTraceSpectralGap.transversalSet n := hx
        have hstateA : state ∈ TransversalTraceSpectralGap.transversalSet n := by
          simpa only [TransversalTraceSpectralGap.transversalSet, Finset.mem_filter,
            Finset.mem_univ, true_and] using htrans
        have hmix := ScheduledTransversalTraceMixing.scheduled_transversal_trace_mixing
          n r M₁ M₂ o₁ o₂ p j (current.tables j) hn hfull hr h₁ h₂ hj htable
          (hgood.1 j le_rfl) x state hxA hstateA
        simpa only [P, A, TransversalTraceSpectralGap.transversalSet, s, bound,
          stateWeight, htrans, weightOfKind,
          Arlib.Computation.Charged.val_bind, CountingMatroid.Model.Operations.natSub,
          Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure,
          BoundedRunResourceEnvelope.ratPower_value, Option.getD_some,
          Rat.cast_pow] using hmix

end CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · reduced · proved ScheduledTransversalTraceMixing.scheduled_transversal_trace_mixing and used it to close the positive-phase analytical conjunct. Only capped finite-suffix final-stage coupling remains; its existing child imports this parent, so its definitions must be decoupled before that child can be applied here.

* 2026-10-09 · reduced · proved the factor-two transversal-to-operational comparison and the covered phase-zero finite-suffix mass bound; the target now closes at phase zero as well as off transversals. Positive-phase trace mixing and its operational finite-suffix coupling remain in the original theorem; no new open helper.

* 2026-10-08 · retained · live handoff recorded-path-domination-20261008-wave1 was mechanically rejected; the warm transversal comparison remains owned here. Restriction proves only zero off the transversal class, not its endpoint density bound.

* 2026-10-08 · decomposed · exact finite-suffix restart marginal; invalid endpoints have zero mass by restartPhase_transversal. The transversal warm endpoint comparison needs the trace mixing and finite-bit transfer.
-/
