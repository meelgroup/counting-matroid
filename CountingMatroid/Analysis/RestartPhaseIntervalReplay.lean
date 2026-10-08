import CountingMatroid.Analysis.ChainStepIntervalReplay
import CountingMatroid.Analysis.TraceReturnIntervalReplay
import CountingMatroid.Analysis.InitialRestartLaw

set_option autoImplicit false

/-!
Successful capped phase restarts have monotone fair-bit cursors and replay
from their consumed intervals. The proof composes the exact fresh transversal
scan, capped trace-return replay, and the two nested absorbing-option folds.
No probability estimate or independence premise is assumed here.
-/

namespace CountingMatroid.Analysis.RestartPhaseIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepIntervalReplay

/-- INTERNAL: A successful capped restart has a monotone fair-bit cursor and
replays from exactly the interval consumed, including all trace-return stages.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restartPhase_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (tables : LearnedWeights n) (j start : ℕ) :
    SuccessReplay (fun tape => (restartPhase r o₁ o₂ tape s tables j start).val)
      Prod.snd start := by
  let stage : (ℕ → Bool) → Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell (Option (RestartCursor n)) :=
    fun tape current index => do
      match current with
      | none => pure none
      | some current =>
          let a ← CountingMatroid.Model.Operations.successor index
          let q ← ratPower s.ρ a
          let weights ← CountingMatroid.Model.Operations.learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ current => do
            match current with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q weights current)
            s.τ (some current)
  let cross := fun tape current =>
    (Arlib.Computation.Charged.foldl (stage tape) (List.range j) (some current)).val
  have hcross : ∀ current, SuccessReplay (fun tape => cross tape current)
      RestartCursor.bitCursor current.bitCursor := by
    intro current
    apply foldl_successReplay
    · intro tape a
      rfl
    · intro current index
      dsimp only [stage]
      simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
      apply foldl_successReplay
      · intro tape a
        rfl
      · intro current a
        exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s _ _ current
  intro tape out hrun
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape start).val.1, (freshTransversal n tape start).val.2, 0⟩
  unfold restartPhase at hrun
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor] at hrun
  change (match cross tape initial with
    | none => pure none
    | some result => pure (some (result.state, result.bitCursor)) :
      Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val = some out at hrun
  cases hresult : cross tape initial with
  | none =>
      simp only [hresult, Arlib.Computation.Charged.val_pure] at hrun
      contradiction
  | some result =>
      simp only [hresult, Arlib.Computation.Charged.val_pure] at hrun
      have hout : (result.state, result.bitCursor) = out := Option.some.inj hrun
      subst out
      have hlocal := hcross initial tape result hresult
      have hinit : initial.bitCursor = start + n := by
        simp only [initial, InitialRestartLaw.freshTransversal_value]
      have hstart : start ≤ initial.bitCursor := by rw [hinit]; omega
      refine ⟨hstart.trans hlocal.1, ?_⟩
      intro other hagree
      have hfresh : (freshTransversal n other start).val =
          (freshTransversal n tape start).val := by
        rw [InitialRestartLaw.freshTransversal_value, InitialRestartLaw.freshTransversal_value]
        congr 1
        apply Finset.image_congr
        intro i _
        change (i, other (start + i.val)) = (i, tape (start + i.val))
        congr 1
        exact (hagree (start + i.val) (by omega) (by
          have hi := i.isLt
          rw [hinit] at hlocal
          omega)).symm
      have heq := hlocal.2 other (fun i hlo hhi => hagree i (hstart.trans hlo) hhi)
      dsimp only at heq
      unfold restartPhase
      simp only [Arlib.Computation.Charged.val_bind, hfresh,
        Arlib.Computation.Charged.repeatFor]
      change (match cross other initial with
        | none => pure none
        | some result => pure (some (result.state, result.bitCursor)) :
      Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val =
          some (result.state, result.bitCursor)
      rw [heq]
      rfl

end CountingMatroid.Analysis.RestartPhaseIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · after rejected handoff, proved traceReturn locality and lifted
  it through both nested restart folds; no unproved supporting declaration remains.
* r21 · rejected handoff · r21-restart-interval-replay-1 was mechanically rejected
  without diagnostic; retained ownership and continued the proof locally.
-/
