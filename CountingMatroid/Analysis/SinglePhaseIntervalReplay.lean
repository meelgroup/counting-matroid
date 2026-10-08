import CountingMatroid.Analysis.BoundedRunPhase
import CountingMatroid.Analysis.ObservePhaseIntervalReplay
import CountingMatroid.Analysis.RestartPhaseIntervalReplay

set_option autoImplicit false

/-!
The actual bounded-run phase composes restart and observation replay with its
deterministic finalization. The proof is uniform in an arbitrary schedule.
-/

namespace CountingMatroid.Analysis.SinglePhaseIntervalReplay
open CountingMatroid.Model

/-- INTERNAL: Compose restart and observation interval replay through the
actual deterministic finish, product, and table-write suffix of a phase.
TEXLINE: main.tex:1163-1201,1392-1421 -/
theorem single_phase_interval_replay {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) :
    ∀ a (tape : ℕ → Bool) (previous next : CountingMatroid.Program.AnnealingCursor n),
      (BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s a (some previous)).val = some next →
      previous.bitCursor ≤ next.bitCursor ∧
        ∀ other : ℕ → Bool,
          (∀ i, previous.bitCursor ≤ i → i < next.bitCursor → tape i = other i) →
          (BoundedRunPhase.boundedRunPhase r o₁ o₂ other s a (some previous)).val = some next := by
  intro a tape previous next hrun
  unfold BoundedRunPhase.boundedRunPhase at hrun
  simp only [Arlib.Computation.Charged.val_bind] at hrun
  cases hstarted : (CountingMatroid.Program.restartPhase r o₁ o₂ tape
      s previous.tables a
      previous.bitCursor).val with
  | none =>
      simp only [hstarted, Arlib.Computation.Charged.val_pure] at hrun
      contradiction
  | some started =>
      simp only [hstarted, Arlib.Computation.Charged.val_bind] at hrun
      cases hobserved : (CountingMatroid.Program.observePhase r o₁ o₂ tape
          s
          (CountingMatroid.Program.ratPower
            s.ρ a).val
          previous.currentWeights started).val with
      | none =>
          simp only [hobserved, Arlib.Computation.Charged.val_pure] at hrun
          contradiction
      | some observed =>
          simp only [hobserved, Arlib.Computation.Charged.val_bind] at hrun
          have hcursor : next.bitCursor = observed.bitCursor := by
            cases hfinished : (CountingMatroid.Program.finishPhase
                s a
                previous.currentWeights observed).val with
            | none =>
                simp only [hfinished, Arlib.Computation.Charged.val_pure] at hrun
                contradiction
            | some result =>
                cases result with
                | mk ratio weights =>
                  simp only [hfinished, Arlib.Computation.Charged.val_bind] at hrun
                  by_cases hupdate : (CountingMatroid.Model.Operations.lessThan
                      (CountingMatroid.Model.Operations.successor a).val
                      s.L).val = true
                  · rw [if_pos hupdate] at hrun
                    simp only [Arlib.Computation.Charged.val_bind] at hrun
                    exact (congrArg CountingMatroid.Program.AnnealingCursor.bitCursor
                      (Option.some.inj hrun)).symm
                  · rw [if_neg hupdate] at hrun
                    exact (congrArg CountingMatroid.Program.AnnealingCursor.bitCursor
                      (Option.some.inj hrun)).symm
          have hrestart := RestartPhaseIntervalReplay.restartPhase_success_interval
            r o₁ o₂ s
            previous.tables a previous.bitCursor tape started hstarted
          have hobservation := ObservePhaseIntervalReplay.observePhase_success_interval
            r o₁ o₂ s
            (CountingMatroid.Program.ratPower
              s.ρ a).val
            previous.currentWeights started tape observed hobserved
          refine ⟨hrestart.1.trans (hobservation.1.trans hcursor.symm.le), ?_⟩
          intro other hagree
          have hs := hrestart.2 other (fun i hlo hhi => hagree i hlo
            (hhi.trans_le (hobservation.1.trans hcursor.symm.le)))
          have ho := hobservation.2 other (fun i hlo hhi => hagree i
            (hrestart.1.trans hlo) (hhi.trans_le hcursor.symm.le))
          dsimp only at hs ho
          unfold BoundedRunPhase.boundedRunPhase
          simp only [Arlib.Computation.Charged.val_bind, hs, ho]
          exact hrun

end CountingMatroid.Analysis.SinglePhaseIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · single-phase replay by composing the proved restart and
  observation invariants; evaluated both deterministic table-update branches.
-/
