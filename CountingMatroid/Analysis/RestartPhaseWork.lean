import CountingMatroid.Analysis.PhaseChainWork

set_option autoImplicit false
namespace CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: A fresh transversal requires one bit, one insertion, and one
cursor increment per ground position. TEXLINE: main.tex:1431-1439 -/
theorem freshTransversal_otherSteps_le (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    otherSteps (freshTransversal n tape cursor) ≤ n * (2 * n + 3) := by
  unfold freshTransversal
  apply (otherSteps_foldl_le_of_mem _ _ (2 * n + 3) ?_ _).trans_eq (by simp)
  intro acc i hi
  simp [otherSteps_bind, fairBit, insertPaired, successor]; omega

/-- INTERNAL: A trace call performs at most its cap many guarded chain steps,
including the interrupted and aborted branches. TEXLINE: main.tex:1428-1439 -/
theorem traceReturn_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : RestartCursor n) (K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (traceReturn r o₁ o₂ tape s q weights start) ≤
      s.restartCap * (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3) := by
  unfold traceReturn
  rw [otherSteps_bind]
  split <;> simp only [work_pure, Nat.add_zero]
  all_goals
    unfold Arlib.Computation.Charged.repeatWhile
    apply (otherSteps_foldlWhile_le _ _ _
      (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3) ?_).trans_eq (by simp)
    intro acc index
    dsimp only
    split
    · simp
    · split
      · simp
      · rename_i current he
        have hc := chainStep_otherSteps_le r o₁ o₂ tape s.drawTrials q weights
          current.state current.bitCursor K hq hw
        simp only [otherSteps_bind]
        split
        · simp only [otherSteps_bind]
          split
          · simp [lessThan, successor] at *; omega
          · rename_i state bitCursor he
            have hk := classifyState_otherSteps_le state
            simp only [otherSteps_bind]
            split <;> simp [lessThan, successor, work_map] at * <;> omega
        · simp [lessThan]

/-- INTERNAL: Restart work is bounded by its explicit nested loop caps, powers,
table reads, and the uniform trace-call bound. TEXLINE: main.tex:1428-1439 -/
theorem restartPhase_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor K : ℕ)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + j * binaryRatLength s.ρ) ≤ K)
    (hw : ∀ phase i, binaryRatLength (tables phase i) ≤ K) :
    otherSteps (restartPhase r o₁ o₂ tape s tables j cursor) ≤
      n * (2 * n + 3) + j *
        (1 + j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 +
          (s.L * n * n + 1) +
          s.τ * (s.restartCap *
            (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3))) := by
  have htrace (index : ℕ) (hi : index < j) (current : RestartCursor n) :
      otherSteps (traceReturn r o₁ o₂ tape s (ratPower s.ρ (index + 1)).val
        (tables (index + 1)) current) ≤
        s.restartCap * (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3) := by
    apply traceReturn_otherSteps_le r o₁ o₂ tape s _ _ current K _ (hw _)
    have hl := ratPower_binary_length_le s.ρ (index + 1)
    have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) (show index + 1 ≤ j by omega)
    have hn := Nat.mul_le_mul_left n (show binaryRatLength (ratPower s.ρ (index + 1)).val ≤
      binaryRatLength 1 + j * binaryRatLength s.ρ by omega)
    omega
  unfold restartPhase
  rw [otherSteps_bind, otherSteps_bind]
  have hf := freshTransversal_otherSteps_le n tape cursor
  split <;> simp only [work_pure, Nat.add_zero]
  all_goals
    apply Nat.add_le_add hf
    unfold Arlib.Computation.Charged.repeatFor
    apply (otherSteps_foldl_le_of_mem _ _
      (1 + j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 +
        (s.L * n * n + 1) +
        s.τ * (s.restartCap *
          (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3))) ?_ _).trans_eq (by simp)
    intro acc index hi
    have hi' : index + 1 ≤ j := by simpa using hi
    cases acc with
    | none => simp
    | some current =>
        have hp : otherSteps (ratPower s.ρ (index + 1)) ≤
            j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 := by
          apply (ratPower_otherSteps_le s.ρ _).trans
          exact Nat.mul_le_mul hi' (Nat.pow_le_pow_left (by gcongr) 2)
        simp only [otherSteps_bind, successor, learnedWeightRead,
          Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany,
          work_word, work_words]
        have hsum : 1 + otherSteps (ratPower s.ρ (index + 1)) +
            (s.L * n * n + 1) ≤
            1 + j * (binaryRatLength 1 + j * binaryRatLength s.ρ) ^ 2 +
              (s.L * n * n + 1) := by omega
        rw [← Nat.add_assoc, ← Nat.add_assoc]
        apply Nat.add_le_add hsum
        try unfold Arlib.Computation.Charged.repeatFor
        apply (otherSteps_foldl_le_of_mem _ _
          (s.restartCap * (chainBudget n s.drawTrials K + n * (4 * n + 3) + 3))
          ?_ _).trans_eq (by simp)
        intro c a ha
        cases c with
        | none => simp
        | some c => exact htrace index (by omega) c
end CountingMatroid.Analysis.RestartPhaseWork
