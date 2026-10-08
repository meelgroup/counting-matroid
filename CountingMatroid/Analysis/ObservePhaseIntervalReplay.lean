import CountingMatroid.Analysis.ChainStepIntervalReplay

set_option autoImplicit false

/-!
Successful observation trajectories have monotone cursors and replay from the
consumed interval. Recording a state reads no tape, while each transition uses
the proved chain-step invariant. An aborted observation remains absorbing.
-/

namespace CountingMatroid.Analysis.ObservePhaseIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: Recording an observation preserves its fair-bit cursor exactly.
TEXLINE: main.tex:1181-1187 -/
private theorem recordObservation_cursor {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    next.bitCursor = current.bitCursor := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · cases h
  · simp only [Arlib.Computation.Charged.val_bind] at h
    exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm
  · simp only [Arlib.Computation.Charged.val_bind] at h
    exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm

/-- INTERNAL: Replay a successful correlated-observation loop from the interval
it consumed, retaining every state count and its numerator sum.
TEXLINE: main.tex:1181-1187,1392-1421 -/
theorem observePhase_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (start : PairedSet n × ℕ) :
    SuccessReplay (fun tape => (observePhase r o₁ o₂ tape s q weights start).val)
      ObservationCursor.bitCursor start.2 := by
  unfold observePhase
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
  apply foldl_successReplay
  · intro tape a
    rfl
  · intro current index tape next hrun
    simp only [Arlib.Computation.Charged.val_bind] at hrun
    by_cases hstart : (natEqual index 0).val = true
    · rw [if_pos hstart] at hrun
      have hcursor := recordObservation_cursor r o₁ o₂ s.ρ current next hrun
      refine ⟨hcursor.symm.le, ?_⟩
      intro other _
      simp only [Arlib.Computation.Charged.val_bind]
      rw [if_pos hstart]
      exact hrun
    · rw [if_neg hstart] at hrun
      simp only [Arlib.Computation.Charged.val_bind] at hrun
      cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q weights
          current.state current.bitCursor).val with
      | none =>
          simp only [hchain, Arlib.Computation.Charged.val_pure] at hrun
          contradiction
      | some step =>
          simp only [hchain] at hrun
          have hcursor := recordObservation_cursor r o₁ o₂ s.ρ
            ⟨step.1, step.2, current.counts, current.numeratorSum⟩ next hrun
          have hlocal := chainStep_success_interval r o₁ o₂ s.drawTrials q weights
            current.state current.bitCursor tape step hchain
          refine ⟨hlocal.1.trans hcursor.symm.le, ?_⟩
          intro other hagree
          have heq := hlocal.2 other (by simpa only [hcursor] using hagree)
          simp only [Arlib.Computation.Charged.val_bind]
          rw [if_neg hstart]
          simp only [Arlib.Computation.Charged.val_bind]
          dsimp only at heq
          rw [heq]
          cases step
          exact hrun

end CountingMatroid.Analysis.ObservePhaseIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · observation-loop interval replay, using exact cursor
  preservation by recording and successful chain-step replay.
-/
