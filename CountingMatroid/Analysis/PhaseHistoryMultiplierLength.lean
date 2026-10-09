import CountingMatroid.Analysis.PhaseResourcePrimitives
import CountingMatroid.Analysis.FinishPhaseWeightsSize
import CountingMatroid.Analysis.BoundedRunPhaseHistory

set_option autoImplicit false

namespace CountingMatroid.Analysis.PhaseHistoryMultiplierLength

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.BoundedRunPhaseHistory

/-- INTERNAL: Keep the additive multiplier-scan bound through the actual
history, including writes to the learned tables. No product-size budget is
needed for a draw denominator. TEXLINE: main.tex:1356-1390 -/
theorem phase_history_multiplier_length_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n)
    (h : phaseHistory r o₁ o₂ tape s j = some current) :
    (∀ index, binaryRatLength (current.currentWeights index) ≤
      6 + j * (n * n * (4 * (s.observations + 4)))) ∧
    (∀ phase index, binaryRatLength (current.tables phase index) ≤
      6 + j * (n * n * (4 * (s.observations + 4)))) := by
  induction j generalizing current with
  | zero =>
      have he : initialCursor n s = current := Option.some.inj h
      subst current
      have hfour : binaryRatLength (4 : ℚ) = 6 := by decide
      simp only [initialCursor, initialWeights, allocateLearnedWeights,
        Arlib.Computation.Charged.val_opMany, hfour, Nat.zero_mul, Nat.add_zero,
        le_refl, implies_true, and_self]
  | succ j ih =>
      rw [phaseHistory_succ] at h
      cases hp : phaseHistory r o₁ o₂ tape s j with
      | none => simp [hp, boundedRunPhase] at h
      | some previous =>
          rw [hp] at h
          obtain ⟨hw, ht⟩ := ih previous hp
          unfold boundedRunPhase at h
          simp only [Arlib.Computation.Charged.val_bind] at h
          cases hs : (restartPhase r o₁ o₂ tape s previous.tables j
              previous.bitCursor).val with
          | none => simp [hs] at h
          | some started =>
              simp only [hs, Arlib.Computation.Charged.val_bind] at h
              cases ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
                  previous.currentWeights started).val with
              | none => simp [ho] at h
              | some observed =>
                  simp only [ho, Arlib.Computation.Charged.val_bind] at h
                  cases hf : (finishPhase s j previous.currentWeights observed).val with
                  | none => simp [hf] at h
                  | some finished =>
                      simp only [hf, Arlib.Computation.Charged.val_bind] at h
                      have hc := BoundedRunResourceEnvelope.observePhase_counts_le
                        r o₁ o₂ tape s (ratPower s.ρ j).val
                        previous.currentWeights started observed ho
                      have hn := FinishPhaseWeightsSize.finishPhase_weights_length_le
                        s j _ previous.currentWeights observed hc hw
                        finished.1 finished.2 hf
                      have hn' : ∀ index, binaryRatLength (finished.2 index) ≤
                          6 + (j + 1) * (n * n * (4 * (s.observations + 4))) := by
                        intro index
                        simpa only [Nat.add_mul, Nat.one_mul, Nat.add_assoc] using hn index
                      simp only [ratMul, successor, lessThan,
                        Arlib.Computation.Charged.val_opMany,
                        Arlib.Computation.Charged.val_op] at h
                      by_cases hu : j + 1 < s.L
                      · simp only [hu, decide_true, ite_true] at h
                        simp only [Arlib.Computation.Charged.val_bind,
                          Arlib.Computation.Charged.val_pure, Option.some.injEq] at h
                        subst current
                        refine ⟨hn', ?_⟩
                        intro phase index
                        simp only [learnedWeightWrite, Arlib.Computation.Charged.val_opMany]
                        split_ifs
                        · exact hn' index
                        · exact (ht phase index).trans (by
                            apply Nat.add_le_add_left
                            exact Nat.mul_le_mul_right _ (Nat.le_succ j))
                      · simp only [hu, decide_false, Bool.false_eq_true, ite_false] at h
                        simp only [Arlib.Computation.Charged.val_pure,
                          Option.some.injEq] at h
                        subst current
                        refine ⟨hn', ?_⟩
                        intro phase index
                        exact (ht phase index).trans (by
                          apply Nat.add_le_add_left
                          exact Nat.mul_le_mul_right _ (Nat.le_succ j))

end CountingMatroid.Analysis.PhaseHistoryMultiplierLength

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved the additive multiplier-scan budget through actual history and learned-table writes, without the coarse runSize power.
-/
