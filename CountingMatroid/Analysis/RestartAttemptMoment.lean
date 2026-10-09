import CountingMatroid.Analysis.RestartAttemptAccounting
import CountingMatroid.Analysis.PositiveTimeTraceKernel
import CountingMatroid.Analysis.IdealExchangeChain
import CountingMatroid.Analysis.AnnealingPartitionDrift
import CountingMatroid.Analysis.StationaryReturnOccupation
import CountingMatroid.Analysis.TypeMassLowerBounds

set_option autoImplicit false

/-!
The stochastic half of the restart certificate now bounds a fixed,
value-preserving stopped attempt counter. The zero-stage case is proved.
Finite stationary excursion occupation budgets and their numerical bounds
are proved. Positive stages require only the operational occupation comparison
with those fixed budgets, including warm stage propagation. Constructing
covered integer-draw histories is a separate deterministic obligation.
-/
namespace CountingMatroid.Analysis.RestartAttemptMoment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: Transfer the paper's uncapped restart mean to the fixed counted
restart on the actual suffix, retaining attempts made before a draw abort.
The reached-history witness fixes both tables and cursor, rather than letting
the expectation proof choose an unrelated cost function.
TEXLINE: main.tex:1072-1087,1207-1234,1392-1421 -/
theorem restart_attempt_moment (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℚ)) /
      (2 : ℚ) ^ t ≤ 20 * (n : ℚ) ^ 2 * (s.L : ℚ) * (s.τ : ℚ) := by
  dsimp only
  cases j with
  | zero =>
      simp only [prefixAttemptCost, countedRestart,
        Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
        Arlib.Computation.Charged.repeatFor, List.range_zero,
        Arlib.Computation.Charged.val_foldl_nil, Nat.cast_zero,
        Finset.sum_const_zero, zero_div]
      positivity
  | succ a =>
      classical
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      let q (i : Fin (a + 1)) := s.ρ ^ (i.val + 1)
      let w (i : Fin (a + 1)) := history.current.tables (i.val + 1)
      have hq (i : Fin (a + 1)) : 0 < q i :=
        pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 _
      have hgood (i : Fin (a + 1)) := history.good.1 (i.val + 1) (by omega)
      have hw (i : Fin (a + 1)) (index : DefectIndex n) : 0 < w i index := by
        have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (q i) := by
          apply Finset.sum_pos
          · intro A _
            exact pow_pos (hq i) _
          · exact Finset.univ_nonempty
        exact (div_pos (div_pos hC
          (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (q i) (hq i) index))
          (by norm_num : (0 : ℚ) < 4)).trans_le (hgood i index).1
      let μ (i : Fin (a + 1)) :=
        IdealExchangeChain.operationalLaw r o₁ o₂ (q i) (w i) (hq i) (hw i)
      let P (i : Fin (a + 1)) :=
        IdealExchangeChain.idealChain r o₁ o₂ (q i) (w i) hn (hq i) (hw i)
      let A : Finset (PairedSet n) :=
        Finset.univ.filter (fun state => (classifyState state).val = .transversal)
      let mass (i : Fin (a + 1)) := ∑ x ∈ A, μ i x
      let budget (i : Fin (a + 1)) :=
        4 / mass i * StationaryReturnOccupation.returnOccupation (P i) A (μ i) s.restartCap
      have hbudget (i : Fin (a + 1)) : budget i ≤ 20 * (n : ℝ) ^ 2 := by
        have hmass_eq : mass i =
            (StationaryMeanIdentities.typeMean r o₁ o₂ (q i) (w i) .transversal : ℝ) := by
          rw [← IdealExchangeChain.operational_type_mean r o₁ o₂ (q i) (w i)
            (hq i) (hw i) .transversal]
          simp only [mass, A, μ, Arlib.Probability.FinDist.Ex,
            IdealExchangeChain.typeIndicator, mul_ite, mul_one, mul_zero]
          exact Finset.sum_filter _ _
        have hmass_lower : 1 / (5 * (n : ℝ) ^ 2) ≤ mass i := by
          rw [hmass_eq]
          have hb := (Rat.cast_le (K := ℝ)).mpr
            (TypeMassLowerBounds.good_type_mass_bounds r o₁ o₂
              (q i) (w i) hn (hq i) (hgood i)).2.1
          push_cast at hb
          exact hb
        have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
        have hmass : 0 < mass i :=
          (by positivity : (0 : ℝ) < 1 / (5 * (n : ℝ) ^ 2)).trans_le hmass_lower
        have hB : 1 ≤ (5 * (n : ℝ) ^ 2) * mass i := by
          have hb := (div_le_iff₀ (by positivity : (0 : ℝ) < 5 * (n : ℝ) ^ 2)).mp hmass_lower
          simpa only [mul_comm] using hb
        have hb := StationaryReturnOccupation.warm_return_occupation_le
          (P i) A (μ i)
          (IdealExchangeChain.ideal_chain_stationary r o₁ o₂ (q i) (w i) hn (hq i) (hw i))
          s.restartCap 4 (5 * (n : ℝ) ^ 2) (by norm_num) hmass hB
        change budget i ≤ 4 * (5 * (n : ℝ) ^ 2) at hb
        nlinarith
      have hcomparison :
          (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
            (2 : ℝ) ^ t ≤ (s.τ : ℝ) * ∑ i : Fin (a + 1), budget i := by
        /- PARKED: Recovery boundary is now the actual finite-tape occupation
        comparison displayed above, not Kac's bound or arithmetic. All stage
        kernels, stationary laws, horizons and budgets are fixed from the
        actual history; hbudget proves each budget <= 20*n^2.
        Next step: split countedStage/countedReturn into attempted-transition
        indicators on stopped adaptive bit prefixes, including the indicator
        for a chainStep whose draw aborts. Dominate each indicator by the
        corresponding uncapped positive-time survival tail with starting
        sublaw <= 4 times the normalized transversal law. Propagate that
        sublaw at stage boundaries by scheduled trace mixing and partition
        drift. H = restartCap overcounts one possible tail and is safe.
        Failed routes: (1) expanding the charged fold exposes only its final
        counter, with no prefix disintegration; (2) endpoint subkernel
        domination controls completed returns only, and discards the final
        attempt on a draw abort. Neither proves this occupation comparison.
        Required unavailable bridge: a stopped attempt-prefix subkernel (or
        finite-tape survival comparison), preserving aborted draw tokens.
        RestartAttemptDrawCover constructs draw sites but does not supply
        their stopped occupation masses. No new unproved child is introduced.
        -/
        sorry
      have htotal :
          (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
            (2 : ℝ) ^ t ≤ 20 * (n : ℝ) ^ 2 * (s.L : ℝ) * (s.τ : ℝ) := by
        apply hcomparison.trans
        calc
          (s.τ : ℝ) * (∑ i : Fin (a + 1), budget i) ≤
              (s.τ : ℝ) * ∑ _i : Fin (a + 1), 20 * (n : ℝ) ^ 2 :=
            mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun i _ => hbudget i) (by positivity)
          _ = 20 * (n : ℝ) ^ 2 * ((a + 1 : ℕ) : ℝ) * (s.τ : ℝ) := by simp; ring
          _ ≤ 20 * (n : ℝ) ^ 2 * (s.L : ℝ) * (s.τ : ℝ) := by
            have hjreal : ((a + 1 : ℕ) : ℝ) ≤ (s.L : ℝ) := by exact_mod_cast hj.le
            exact mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hjreal (by positivity)) (by positivity)
      apply (Rat.cast_le (K := ℝ)).mp
      push_cast
      exact htotal

end CountingMatroid.Analysis.RestartAttemptMoment

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · repaired decomposition · proved finite stationary return occupation telescoping and its warm budget, instantiated every actual stored stage, and isolated the stopped finite-tape occupation comparison; preserved the theorem statement and its single open proof.

* 2026-10-09 · reduced · fixed the quantity to the proved restart instrument, closed zero stages, and exposed the positive-stage stopped-counter sum. Remaining work is occupation/survival comparison and warm stage propagation, not selection of a cost witness or construction of draw histories.
-/
