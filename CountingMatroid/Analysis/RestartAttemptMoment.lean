import CountingMatroid.Analysis.RestartAttemptAccounting
import CountingMatroid.Analysis.PositiveTimeTraceKernel
import CountingMatroid.Analysis.IdealExchangeChain
import CountingMatroid.Analysis.AnnealingPartitionDrift
import CountingMatroid.Analysis.StationaryReturnOccupation
import CountingMatroid.Analysis.TypeMassLowerBounds
import CountingMatroid.Analysis.RestartStageAttemptMean

set_option autoImplicit false

/-!
The stochastic half of the restart certificate: the finite-suffix mean of the
fixed, value-preserving stopped attempt counter is at most `20 n² L τ`.
The mean splits exactly into stage means (draw-abort attempts retained); each
stage's increment is identified with the attempt count of its τ actual returns,
whose mean `RestartStageAttemptMean.restart_stage_attempt_mean` bounds by τ warm
stationary occupation budgets, each at most `20 n²`. Constructing covered
integer-draw histories is a separate deterministic obligation.
-/
namespace CountingMatroid.Analysis.RestartAttemptMoment

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: The actual stopped restart accumulator after k stored stages,
using the same fresh initializer and suffix throughout. The count is retained
when the cursor becomes none, including the last draw-abort token.
TEXLINE: main.tex:1163-1176,1226-1234 -/
noncomputable def prefixRestartState {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) : Option (RestartCursor n) × ℕ :=
  let tape := fun i => ((pref ++ suffix)[i]?).getD false
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let initial := (freshTransversal n tape history.current.bitCursor).val
  (Arlib.Computation.Charged.repeatFor
    (fun index acc => countedStage r o₁ o₂ tape s history.current.tables index acc)
    k (some ⟨initial.1, initial.2, 0⟩, 0)).val

/-- INTERNAL: A stage's retained count increment, formed in the reals so
that its exact telescoping identity needs no truncated-subtraction premise.
TEXLINE: main.tex:1226-1234 -/
noncomputable def prefixStageAttempts {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) : ℝ :=
  ((prefixRestartState history suffix (k + 1)).2 : ℝ) -
    ((prefixRestartState history suffix k).2 : ℝ)

/-- INTERNAL: Split the charged stage fold without dropping an abort count. -/
private theorem attempt_fold_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Each stage increment is evaluated from the actual earlier
stopped accumulator, rather than from a separately chosen starting law.
TEXLINE: main.tex:1226-1234 -/
theorem restart_stage_state_succ {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) :
    prefixRestartState history suffix (k + 1) =
      (countedStage r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables k
        (prefixRestartState history suffix k)).val := by
  unfold prefixRestartState Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, attempt_fold_append]
  rfl

/-- INTERNAL: An early-break fold preserves any natural-valued score
that each continuing body result increases. Refusing continuation keeps it. -/
private theorem attempt_while_mono {α β : Type}
    (f : β → α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell (Option β)) (score : β → ℕ)
    (h : ∀ b a next, (f b a).val = some next → score b ≤ score next)
    (xs : List α) (b : β) :
    score b ≤ score (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact le_rfl
  | cons a xs ih =>
      cases hf : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at hf ⊢
          simp only [Arlib.Computation.Charged.foldlWhile, hf]
          exact le_rfl
      | some next =>
          have hn := (h b a next hf).trans (ih next)
          simp only [Arlib.Computation.Charged.val] at hf hn ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hn

/-- INTERNAL: A fixed fold preserves a score increased by each body. -/
private theorem attempt_fold_mono {α β : Type}
    (f : β → α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell β) (score : β → ℕ)
    (h : ∀ b a, score b ≤ score (f b a).val) (xs : List α) (b : β) :
    score b ≤ score (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b with
  | nil => exact le_rfl
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact (h b a).trans (ih (f b a).val)

/-- INTERNAL: The return's auxiliary count increases even if its cursor
is discarded by a draw abort or the attempt cap.
TEXLINE: main.tex:1163-1176 -/
private theorem counted_return_count_mono {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (w : Multipliers n) (start : RestartCursor n) (count : ℕ) :
    count ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 := by
  apply attempt_while_mono
    (fun acc (_ : ℕ) => countedBody r o₁ o₂ tape s q w acc) Prod.snd
    _ (List.range s.restartCap) ((some start, false), count)
  intro b a next hnext
  simp only [countedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure] at hnext
  cases ht : (traceBody r o₁ o₂ tape s q w b.1).val with
  | none => simp only [ht, Option.map_none] at hnext; contradiction
  | some result =>
      simp only [ht, Option.map_some, Option.some.injEq] at hnext
      rw [← hnext]
      exact Nat.le_add_right _ _

/-- INTERNAL: One stored stage never loses tokens, including when its
stopped cursor is already none.
TEXLINE: main.tex:1163-1176,1226-1234 -/
theorem counted_stage_count_mono {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (tables : LearnedWeights n) (k : ℕ) (acc : Option (RestartCursor n) × ℕ) :
    acc.2 ≤ (countedStage r o₁ o₂ tape s tables k acc).val.2 := by
  simp only [countedStage, Arlib.Computation.Charged.val_bind]
  apply attempt_fold_mono _ Prod.snd _ (List.range s.τ) acc
  intro b a
  cases hb : b.1 with
  | none => simp only [countedTransition, hb, Arlib.Computation.Charged.val_pure]; exact le_rfl
  | some current =>
      simp only [countedTransition, hb]
      exact counted_return_count_mono r o₁ o₂ tape s _ _ current b.2

/-- INTERNAL: The exact real-valued stage difference is a nonnegative
attempt cost on every tape, with no successful-return conditioning.
TEXLINE: main.tex:1230-1234 -/
theorem prefix_stage_attempts_nonneg {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) : 0 ≤ prefixStageAttempts history suffix k := by
  unfold prefixStageAttempts
  rw [sub_nonneg, restart_stage_state_succ]
  exact_mod_cast counted_stage_count_mono r o₁ o₂
    (fun i => ((pref ++ suffix)[i]?).getD false)
    (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables k
    (prefixRestartState history suffix k)

/-- INTERNAL: Stage increments telescope to the original stopped attempt
counter on every suffix, including executions ending in a draw abort.
TEXLINE: main.tex:1230-1234 -/
theorem prefix_stage_attempts_sum {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool) :
    (∑ i : Fin j, prefixStageAttempts history suffix i.val) =
      (prefixAttemptCost history suffix : ℝ) := by
  rw [Fin.sum_univ_eq_sum_range]
  unfold prefixStageAttempts
  rw [Finset.sum_range_sub (fun k => ((prefixRestartState history suffix k).2 : ℝ))]
  have hz : (prefixRestartState history suffix 0).2 = 0 := rfl
  rw [hz, Nat.cast_zero, sub_zero]
  rfl

/-- INTERNAL: The finite-suffix mean is exactly the sum of stage means;
no conditioning on completion removes the last attempt of an abort.
TEXLINE: main.tex:1230-1234,1392-1421 -/
theorem prefix_stage_attempt_mean_sum {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (t : ℕ) :
    (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
      (2 : ℝ) ^ t =
    ∑ i : Fin j, (∑ bits : List.Vector Bool t,
      prefixStageAttempts history bits.val i.val) / (2 : ℝ) ^ t := by
  simp_rw [← prefix_stage_attempts_sum history]
  rw [Finset.sum_comm, Finset.sum_div]

/-- INTERNAL: The cursor of the stopped accumulator after k stages is the
actual restart cursor at the start of stage k.
TEXLINE: main.tex:1163-1176 -/
theorem prefix_state_cursor {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) :
    (prefixRestartState history suffix k).1 =
      RestartStageWarmStart.stageCursor r o₁ o₂
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix))
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
        history.current.bitCursor k 0 := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [RestartStageWarmStart.stage_cursor_next, restart_stage_state_succ,
        ← Prod.mk.eta (p := prefixRestartState history suffix k),
        RestartStageAttemptMean.counted_stage_value, ih]
      rfl

/-- INTERNAL: A stage's real increment is the attempt count of its τ returns.
TEXLINE: main.tex:1163-1176,1230-1234 -/
theorem prefix_stage_attempts_eq {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool)
    (k : ℕ) :
    prefixStageAttempts history suffix k =
      (RestartStageAttemptMean.stageAttempts r o₁ o₂
        (FiniteStoppedFiberMass.finiteTape (pref ++ suffix))
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
        history.current.bitCursor k : ℝ) := by
  unfold prefixStageAttempts
  rw [restart_stage_state_succ,
    ← Prod.mk.eta (p := prefixRestartState history suffix k),
    RestartStageAttemptMean.counted_stage_value, prefix_state_cursor]
  rw [Nat.cast_add, add_sub_cancel_left]
  rfl

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
      have hstage (i : Fin (a + 1)) :
          (∑ bits : List.Vector Bool t,
            prefixStageAttempts history bits.val i.val) / (2 : ℝ) ^ t ≤
              (s.τ : ℝ) * budget i := by
        have hm := RestartStageAttemptMean.restart_stage_attempt_mean n r M₁ M₂ o₁ o₂ p hn
          hfull hr h₁ h₂ (a + 1) hj pref history i.val i.isLt (hq i) (hw i)
        simp_rw [prefix_stage_attempts_eq history]
        exact hm
      have hcomparison :
          (∑ bits : List.Vector Bool t, (prefixAttemptCost history bits.val : ℝ)) /
            (2 : ℝ) ^ t ≤ (s.τ : ℝ) * ∑ i : Fin (a + 1), budget i := by
        rw [prefix_stage_attempt_mean_sum history t, Finset.mul_sum]
        exact Finset.sum_le_sum fun i _ => hstage i
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

* 2026-10-09 · proved · closed the one-stage bound with the (previously unattached, fully proved) `RestartStageAttemptMean.restart_stage_attempt_mean`, bridged by `prefix_state_cursor` and `prefix_stage_attempts_eq`; no `sorry` remains.

* 2026-10-09 · recovered stage decomposition · proved actual stage recurrence, nonnegative retained increments, and exact mean telescoping; replaced the whole-restart occupation gap by the one-stage mean bound, retaining the original theorem and one open proof.

* 2026-10-09 · repaired decomposition · proved finite stationary return occupation telescoping and its warm budget, instantiated every actual stored stage, and isolated the stopped finite-tape occupation comparison; preserved the theorem statement and its single open proof.

* 2026-10-09 · reduced · fixed the quantity to the proved restart instrument, closed zero stages, and exposed the positive-stage stopped-counter sum. Remaining work is occupation/survival comparison and warm stage propagation, not selection of a cost witness or construction of draw histories.
-/
