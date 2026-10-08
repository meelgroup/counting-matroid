import CountingMatroid.Analysis.BoundedRunPhase
import CountingMatroid.Analysis.RationalHeight
import CountingMatroid.Analysis.FinishPhaseWeightsSize

/-!
The phase-size proof handles all abort branches and proves preservation of
current weights, stored tables, and the product from the successful observation
count and ratio-size contracts. The nested multiplier scan is proved in
`FinishPhaseWeightsSize`. The remaining obligation is blocked by the placement
of existing observation and ratio contracts in `BoundedRunResourceEnvelope`,
which depends on this module; those proofs need upstream extraction.
-/

set_option autoImplicit false
namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

/-- INTERNAL: A successful phase grows every rational-size budget by at most
one phase increment; aborts preserve the invariant vacuously. This is a
value-only statement, independent of the charge paid to reach that value.
TEXLINE: main.tex:1356-1390 -/
theorem phase_preserves_size {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    PhaseSizeInvariant (runSize n s) (j + 1)
      (boundedRunPhase r o₁ o₂ tape s j acc).val := by
  cases acc with
  | none => simp [boundedRunPhase, PhaseSizeInvariant]
  | some current =>
      intro next hnext
      dsimp [boundedRunPhase] at hnext
      cases hstarted : (restartPhase r o₁ o₂ tape s current.tables j
        current.bitCursor).val with
      | none => simp [hstarted] at hnext
      | some started =>
          simp only [hstarted, Arlib.Computation.Charged.val_bind] at hnext
          cases hobserved : (observePhase r o₁ o₂ tape s
            (ratPower s.ρ j).val current.currentWeights started).val with
          | none => simp [hobserved] at hnext
          | some observed =>
              simp only [hobserved, Arlib.Computation.Charged.val_bind] at hnext
              cases hfinished : (finishPhase s j current.currentWeights observed).val with
              | none => simp [hfinished] at hnext
              | some finished =>
                  simp only [hfinished, Arlib.Computation.Charged.val_bind] at hnext
                  let S := runSize n s
                  have hS : 2 ≤ S := by dsimp [S, runSize]; omega
                  have hn : n ≤ S := by dsimp [S, runSize]; omega
                  have ho : s.observations ≤ S := by dsimp [S, runSize]; omega
                  have hinc : n * n * (4 * (s.observations + 4)) ≤ S ^ 10 := by
                    have hn2 : n * n ≤ S * S := Nat.mul_le_mul hn hn
                    have hd : 4 * (s.observations + 4) ≤ 20 * S := by omega
                    have hm := Nat.mul_le_mul hn2 hd
                    have hp : 20 ≤ S ^ 7 := by
                      have hp := Nat.pow_le_pow_left hS 7
                      norm_num at hp
                      omega
                    have hb := Nat.mul_le_mul_left (S ^ 3) hp
                    calc
                      n * n * (4 * (s.observations + 4)) ≤ S * S * (20 * S) := hm
                      _ = S ^ 3 * 20 := by ring
                      _ ≤ S ^ 3 * S ^ 7 := hb
                      _ = S ^ 10 := by rw [← pow_add]
                  suffices hcontracts :
                      (∀ kind, observed.counts kind ≤ s.observations) ∧
                      binaryRatLength finished.1 ≤ S ^ 10 by
                    obtain ⟨hw, ht, hp⟩ := hacc current rfl
                    have hweights := FinishPhaseWeightsSize.finishPhase_weights_length_le
                      s j ((j + 1) * S ^ 10) current.currentWeights observed
                      hcontracts.1 hw finished.1 finished.2 hfinished
                    have hwnew (index) : binaryRatLength (finished.2 index) ≤
                        (j + 1 + 1) * S ^ 10 := by
                      have := hweights index
                      nlinarith
                    have hproduct := ScheduleOtherStepsEnvelope.binaryRatLength_mul_le
                      current.product finished.1
                    have hpnew : binaryRatLength (current.product * finished.1) ≤
                        (j + 1 + 1) * S ^ 10 := by
                      have := hcontracts.2
                      dsimp [S] at *
                      nlinarith
                    simp only [ratMul, successor, lessThan,
                      Arlib.Computation.Charged.val_opMany,
                      Arlib.Computation.Charged.val_op] at hnext
                    by_cases hu : j + 1 < s.L
                    · simp only [hu, decide_true, ite_true] at hnext
                      simp only [Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure, Option.some.injEq] at hnext
                      subst next
                      refine ⟨hwnew, ?_, hpnew⟩
                      intro phase index
                      simp only [learnedWeightWrite, Arlib.Computation.Charged.val_opMany]
                      split_ifs
                      · exact hwnew index
                      · have := ht phase index
                        dsimp [S] at *
                        nlinarith
                    · simp only [hu, decide_false, Bool.false_eq_true, ite_false] at hnext
                      simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at hnext
                      subst next
                      refine ⟨hwnew, ?_, hpnew⟩
                      intro phase index
                      have := ht phase index
                      dsimp [S] at *
                      nlinarith
                  -- BLOCKER (import cycle): the count, accumulator-height, and
                  -- ratio contracts are already proved in BoundedRunResourceEnvelope,
                  -- which imports BoundedRunOtherSteps, which imports this file.
                  -- Extract that support upstream rather than duplicating its proofs:
                  -- observePhase_counts_le, observePhase_height_le, and
                  -- finishPhase_ratio_length_le (the last two currently private).
                  -- Their dependency closure also includes chargedFold_count_growth,
                  -- recordObservation_counts_le, recordObservation_height_le,
                  -- ratPower_binary_length_le, and ratPower_value.
                  sorry
end CountingMatroid.Analysis.BoundedRunPhase

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · blocked · proved and built `FinishPhaseWeightsSize.finishPhase_weights_length_le`; reduced the original gap to count and ratio contracts already proved downstream, requiring upstream extraction to avoid an import cycle.
-/
