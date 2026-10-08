import CountingMatroid.Analysis.BoundedRunPhaseHistory

set_option autoImplicit false

/-!
History replay from a deterministic single-phase interval invariant. This
module proves the history induction; it asserts no unproved operational
property of the actual phase. The consuming lower-tail theorem must prove
its phase invariant locally. The monotonicity component is essential: it
allows final-prefix agreement to restrict to every earlier consumed prefix.
-/

namespace CountingMatroid.Analysis.SuccessfulPhaseReplay

open CountingMatroid.Model

/-- INTERNAL: Lift successful single-phase interval replay through the actual
history fold. Agreement below the final cursor is enough; earlier cursor
bounds follow from the successful phase's monotonicity.
TEXLINE: main.tex:1163-1201,1207-1212 -/
theorem successful_history_replay_of_phase_replay {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (hphase : ∀ a (tape : ℕ → Bool) (previous next : CountingMatroid.Program.AnnealingCursor n),
      (BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s a (some previous)).val = some next →
      previous.bitCursor ≤ next.bitCursor ∧
        ∀ otherTape : ℕ → Bool,
          (∀ i, previous.bitCursor ≤ i → i < next.bitCursor → tape i = otherTape i) →
          (BoundedRunPhase.boundedRunPhase r o₁ o₂ otherTape s a (some previous)).val = some next)
    (tapeA : ℕ → Bool) (j : ℕ) (current : CountingMatroid.Program.AnnealingCursor n)
    (hhistory : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tapeA s j = some current)
    (tapeB : ℕ → Bool)
    (hagree : ∀ i < current.bitCursor, tapeA i = tapeB i) :
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tapeB s j = some current := by
  induction j generalizing current with
  | zero =>
      have hcurrent : BoundedRunPhaseHistory.initialCursor n s = current :=
        Option.some.inj hhistory
      exact congrArg some hcurrent
  | succ j ih =>
      rw [BoundedRunPhaseHistory.phaseHistory_succ] at hhistory ⊢
      cases hprevious : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tapeA s j with
      | none =>
          rw [hprevious] at hhistory
          simp only [BoundedRunPhase.boundedRunPhase,
            Arlib.Computation.Charged.val_pure] at hhistory
          contradiction
      | some previous =>
          rw [hprevious] at hhistory
          have hstep := hphase j tapeA previous current hhistory
          rw [ih previous hprevious (fun i hi => hagree i (hi.trans_le hstep.1))]
          exact hstep.2 tapeB (fun i _ hi => hagree i hi)

end CountingMatroid.Analysis.SuccessfulPhaseReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r20 · proved implication · after mechanical handoff rejection without diagnostic, proved the actual-history induction from a precisely stated single-phase interval replay and cursor-monotonicity invariant. The operational obligation remains local to the consuming theorem; this file exports no unproved declaration.
* r20 · open · isolated successful single-phase interval replay and cursor monotonicity. Unfolding the phase reduces the operational proof to the restart/observation loops and their boundedUniform/chainStep success-path locality; the lower-tail parent proves the history induction from this statement.
-/
