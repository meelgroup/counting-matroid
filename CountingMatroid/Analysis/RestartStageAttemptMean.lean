import CountingMatroid.Analysis.RestartStageWarmStart

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
One stored stage of the restart after a reached history. The instrumented
stage adds to its retained counter exactly the attempts of its τ returns,
each made from the actual stopped cursor, including an attempt ending in a
draw abort. On the fresh finite suffix, the mean of that increment is at
most τ times the warm occupation budget 4/π(A) · occupation(π) of the stage's
chain: each return starts from a sublaw at most 4/π(A) times the restricted
stationary law, and makes more than m attempts with at most the ideal
positive-time survival tail.
-/
namespace CountingMatroid.Analysis.RestartStageAttemptMean

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartStageWarmStart
open CountingMatroid.Analysis.ReturnAttemptTail

/-- INTERNAL: Split a charged fold without dropping any value. -/
private theorem stage_fold_append {α β : Type}
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

/-- INTERNAL: Trace folds compose along list concatenation. -/
theorem trace_fold_append {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs ys : List ℕ) (o : Option (RestartCursor n)) :
    traceFold r o₁ o₂ tape s q w (xs ++ ys) o =
      traceFold r o₁ o₂ tape s q w ys (traceFold r o₁ o₂ tape s q w xs o) := by
  unfold traceFold
  exact stage_fold_append _ xs ys o

/-- INTERNAL: Attempts of the τ returns of stage i, each from the actual
stopped cursor before it; aborted cursors contribute nothing further.
TEXLINE: main.tex:1163-1176,1230-1234 -/
noncomputable def stageAttempts {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i : ℕ) : ℕ :=
  ∑ k ∈ Finset.range s.τ,
    ((stageCursor r o₁ o₂ tape s tables cursor i k).map
      (attemptScan r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) s.restartCap)).getD 0

/-- INTERNAL: The instrumented transitions of one stage advance the cursor as
the trace fold and add the attempts of each return to the retained counter.
TEXLINE: main.tex:1163-1176 -/
theorem counted_transition_fold {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (K : ℕ) (o : Option (RestartCursor n)) (count : ℕ) :
    (Arlib.Computation.Charged.foldl
      (fun acc (_ : ℕ) => countedTransition r o₁ o₂ tape s q w acc)
      (List.range K) (o, count)).val =
    (traceFold r o₁ o₂ tape s q w (List.range K) o,
      count + ∑ k ∈ Finset.range K, ((traceFold r o₁ o₂ tape s q w (List.range k) o).map
        (attemptScan r o₁ o₂ tape s q w s.restartCap)).getD 0) := by
  induction K with
  | zero => rfl
  | succ K ih =>
      rw [List.range_succ, stage_fold_append, ih, trace_fold_append,
        Finset.sum_range_succ]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil]
      cases hK : traceFold r o₁ o₂ tape s q w (List.range K) o with
      | none =>
          simp only [countedTransition, Arlib.Computation.Charged.val_pure,
            trace_fold_none, Option.map_none, Option.getD_none, Nat.add_zero]
      | some c =>
          simp only [countedTransition]
          rw [trace_fold_cons]
          ext1
          · rw [countedReturn_projection]
            cases (traceReturn r o₁ o₂ tape s q w c).val <;> rfl
          · rw [counted_return_count]
            simp only [Option.map_some, Option.getD_some]
            omega

/-- INTERNAL: A stored stage's exact instrumented value.
TEXLINE: main.tex:1163-1176 -/
theorem counted_stage_value {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (i : ℕ) (o : Option (RestartCursor n)) (count : ℕ) :
    (countedStage r o₁ o₂ tape s tables i (o, count)).val =
    (traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range s.τ) o,
      count + ∑ k ∈ Finset.range s.τ,
        ((traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range k) o).map
          (attemptScan r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) s.restartCap)).getD 0) := by
  have h := counted_transition_fold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) s.τ o count
  simp only [countedStage, Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, BoundedRunResourceEnvelope.ratPower_value,
    Model.Operations.learnedWeightRead, Arlib.Computation.Charged.val_opMany,
    Arlib.Computation.Charged.repeatFor]
  exact h

/-- INTERNAL: Layer-cake identity for a bounded natural count. -/
theorem nat_layer (c : ℝ) : ∀ (M v : ℕ), v ≤ M →
    (∑ m ∈ Finset.range M, if m + 1 ≤ v then c else 0) = c * v := by
  intro M
  induction M with
  | zero => intro v hv; simp [Nat.le_zero.mp hv]
  | succ M ih =>
      intro v hv
      rw [Finset.sum_range_succ]
      by_cases hvM : v ≤ M
      · rw [ih v hvM, if_neg (by omega), add_zero]
      · have hv' : v = M + 1 := by omega
        subst hv'
        have hsum : (∑ m ∈ Finset.range M, if m + 1 ≤ M + 1 then c else 0) =
            ∑ m ∈ Finset.range M, if m + 1 ≤ M then c else 0 := by
          apply Finset.sum_congr rfl
          intro m hm
          have hm' := Finset.mem_range.mp hm
          rw [if_pos (by omega), if_pos (by omega)]
        rw [hsum, ih M le_rfl, if_pos le_rfl]
        push_cast
        ring

/-- INTERNAL: The finite-suffix mean of a bounded stopped count is the sum of
its upper-tail event masses.
TEXLINE: main.tex:1230-1234 -/
theorem layer_mass {α : Type} (head : List Bool) (t M : ℕ)
    (f : (ℕ → Bool) → Option α) (g : (ℕ → Bool) → α → ℕ)
    (hg : ∀ tape a, g tape a ≤ M) :
    (∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
      ((((f (finiteTape (head ++ bits.val))).map
        (g (finiteTape (head ++ bits.val)))).getD 0 : ℕ) : ℝ)) =
    ∑ m ∈ Finset.range M,
      fairMass head t (fun tape => ∃ a, f tape = some a ∧ m + 1 ≤ g tape a) := by
  classical
  unfold fairMass
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro bits _
  generalize hF : f (finiteTape (head ++ bits.val)) = F
  cases F with
  | none =>
      simp only [Option.map_none, Option.getD_none, Nat.cast_zero, mul_zero]
      symm
      apply Finset.sum_eq_zero
      intro m _
      apply if_neg
      rintro ⟨a, ha, _⟩
      exact absurd (hF.symm.trans ha) (fun h => by cases h)
  | some a =>
      simp only [Option.map_some, Option.getD_some]
      rw [← nat_layer (1 / (2 : ℝ) ^ t) M _ (hg _ a)]
      apply Finset.sum_congr rfl
      intro m _
      by_cases h : m + 1 ≤ g (finiteTape (head ++ bits.val)) a
      · rw [if_pos h, if_pos ⟨a, hF, h⟩]
      · rw [if_neg h, if_neg]
        rintro ⟨a', ha', h'⟩
        cases Option.some.inj (hF.symm.trans ha')
        exact h h'

/-- INTERNAL: One stored stage's finite-suffix mean is at most τ warm
occupation budgets of its own chain.
TEXLINE: main.tex:1072-1087,1219-1234,1392-1421 -/
theorem restart_stage_attempt_mean (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref)
    (i : ℕ) (hi : i < j)
    (hq : 0 < (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ (i + 1))
    (hw : ∀ a, 0 < history.current.tables (i + 1) a) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let π := IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ (i + 1))
      (history.current.tables (i + 1)) hq hw
    let P := IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ (i + 1))
      (history.current.tables (i + 1)) hn hq hw
    let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
    (∑ bits : List.Vector Bool t,
      (stageAttempts r o₁ o₂ (finiteTape (pref ++ bits.val)) s history.current.tables
        history.current.bitCursor i : ℝ)) / (2 : ℝ) ^ t ≤
      (s.τ : ℝ) * (4 / (∑ z ∈ A, π z) *
        StationaryReturnOccupation.returnOccupation P A π s.restartCap) := by
  classical
  intro s t π P A
  let tables := history.current.tables
  let b0 := history.current.bitCursor
  let q := s.ρ ^ (i + 1)
  let w := tables (i + 1)
  let m := CountingMatroid.Model.Run.blockLength n r p
  obtain ⟨C, hlen, _, htotal, hCm, hCstep⟩ :=
    history_prefix_facts n r o₁ o₂ p hn j hj pref history
  change pref.length = b0 at hlen
  change pref.length + t = m at htotal
  change b0 + n + s.restartCap * C ≤ m at hCm
  have hj' : j < s.L := hj
  have hlevel : i + 1 ≤ s.L := by omega
  have hbudget (tape : ℕ → Bool) (k : ℕ) (c : RestartCursor n)
      (h : stageCursor r o₁ o₂ tape s tables b0 i k = some c) :
      Budget s (b0 + n) C c :=
    stage_cursor_budget r o₁ o₂ tape s tables b0 C i
      (fun a ha state start out hs => hCstep a (by omega) tape state start out hs) k c h
  have hinv : ∀ (tape : ℕ → Bool) (current : RestartCursor n) (y : PairedSet n) (stop : ℕ),
      Budget s (b0 + n) C current → current.attempts < s.restartCap →
      (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
        some (y, stop) →
      stop ≤ m ∧ Budget s (b0 + n) C ⟨y, stop, current.attempts + 1⟩ := by
    intro tape current y stop hc ha hs
    have hstop := hCstep (i + 1) hlevel tape current.state current.bitCursor (y, stop) hs
    have hb := budget_step s (b0 + n) C current y stop hc ha hstop
    refine ⟨?_, hb⟩
    obtain ⟨hatt, hcur⟩ := hc
    have hmul : (current.attempts + 1) * C ≤ s.restartCap * C :=
      Nat.mul_le_mul_right C (by omega)
    change stop ≤ current.bitCursor + C at hstop
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  have hcover (tape : ℕ → Bool) (k : ℕ) (c : RestartCursor n)
      (h : stageCursor r o₁ o₂ tape s tables b0 i k = some c) :
      c.bitCursor ≤ pref.length + t := by
    obtain ⟨hatt, hcur⟩ := hbudget tape k c h
    have hmul : c.attempts * C ≤ s.restartCap * C := Nat.mul_le_mul_right C hatt
    rw [htotal]
    omega
  -- The mean of one return's attempts is bounded by tail weights of its start law.
  have hreturn (k : ℕ) :
      (∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((((stageCursor r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i k).map
          (attemptScan r o₁ o₂ (finiteTape (pref ++ bits.val)) s q w s.restartCap)).getD 0 : ℕ)
            : ℝ)) ≤
      ∑ mm ∈ Finset.range (s.restartCap + 1), ∑ x,
        (4 / ∑ z ∈ A, π z) * (if x ∈ A then π x else 0) *
          tailWeight P A mm x := by
    rw [layer_mass pref t (s.restartCap + 1)
      (fun tape => stageCursor r o₁ o₂ tape s tables b0 i k)
      (fun tape c => attemptScan r o₁ o₂ tape s q w s.restartCap c)
      (fun tape c => (attempt_scan_le r o₁ o₂ tape s q w s.restartCap c).trans
        (Nat.le_succ _))]
    apply Finset.sum_le_sum
    intro mm _
    have hf : ChainStepIntervalReplay.SuccessReplay
        (fun tape => stageCursor r o₁ o₂ tape s tables b0 i k)
        RestartCursor.bitCursor pref.length := by
      rw [hlen]
      exact stage_cursor_success_interval r o₁ o₂ s tables b0 i k
    have hbind := FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound pref t
      (fun tape => stageCursor r o₁ o₂ tape s tables b0 i k)
      RestartCursor.bitCursor RestartCursor.state hf
      (fun tape c => mm + 1 ≤ attemptScan r o₁ o₂ tape s q w s.restartCap c)
      (fun x => tailWeight P A mm x) (fun x => tailWeight_nonneg P A mm x)
      (fun bits c hc _ => hcover _ k c hc)
      (by
        intro c hlo hhi head hc
        have hhead : (pref ++ head.val).length = c.bitCursor := by
          simp only [List.length_append, head.2]
          omega
        have hv : (classifyState c.state).val ≠ .invalid := by
          rw [stage_cursor_transversal r o₁ o₂ _ s tables b0 i k c hc]
          intro h
          cases h
        exact attempt_scan_tail r o₁ o₂ s q w P
          (fun head' u x y hx => covered_step_bound r o₁ o₂ s.drawTrials q w hn hq hw
            head' u x y hx)
          (Budget s (b0 + n) C) m hinv s.restartCap mm (pref ++ head.val)
          (t - (c.bitCursor - pref.length)) c hhead.symm
          (by rw [hhead]; omega) hv (hbudget _ k c hc))
    apply hbind.trans
    apply Finset.sum_le_sum
    intro x _
    apply mul_le_mul_of_nonneg_right _ (tailWeight_nonneg P A mm x)
    exact stage_warm_start n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ j hj pref history i hi k
      hq hw x
  have hmean : (∑ bits : List.Vector Bool t,
      (stageAttempts r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i : ℝ)) /
        (2 : ℝ) ^ t =
      ∑ k ∈ Finset.range s.τ, ∑ bits : List.Vector Bool t, (1 / (2 : ℝ) ^ t) *
        ((((stageCursor r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i k).map
          (attemptScan r o₁ o₂ (finiteTape (pref ++ bits.val)) s q w s.restartCap)).getD 0 : ℕ)
            : ℝ) := by
    rw [Finset.sum_div, Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro bits _
    unfold stageAttempts
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro k _
    ring
  change (∑ bits : List.Vector Bool t,
      (stageAttempts r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables b0 i : ℝ)) /
        (2 : ℝ) ^ t ≤ _
  rw [hmean]
  calc
    _ ≤ ∑ _k ∈ Finset.range s.τ, ∑ mm ∈ Finset.range (s.restartCap + 1), ∑ x,
          (4 / ∑ z ∈ A, π z) * (if x ∈ A then π x else 0) * tailWeight P A mm x :=
      Finset.sum_le_sum fun k _ => hreturn k
    _ = (s.τ : ℝ) * (4 / (∑ z ∈ A, π z) *
          StationaryReturnOccupation.returnOccupation P A π s.restartCap) := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
        return_occupation_eq_tail_sum P A π s.restartCap]
      congr 1
      rw [Finset.sum_comm, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro mm _
      ring

end CountingMatroid.Analysis.RestartStageAttemptMean

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · exact instrumented stage value, layer-cake identity for bounded stopped counts, and the stage mean bound from covered attempt tails and factor-four warm starts.
-/
