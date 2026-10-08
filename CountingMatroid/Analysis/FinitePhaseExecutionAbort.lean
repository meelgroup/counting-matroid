import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.InitialRestartLaw
import CountingMatroid.Analysis.FiniteTapeFirstPhaseBound

set_option autoImplicit false

/-!
Normalization of the abort part of the conditional finite-tape phase law.
The live handoff of its quantitative estimate was mechanically rejected.
This module asserts only the proved normalization; the restart and draw
coupling estimate remains local to `finite_tape_lower_tail_bound`.
-/

namespace CountingMatroid.Analysis.FinitePhaseExecutionAbort

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Normalize the conditional execution-abort mass estimate,
retaining every operational failure to obtain good observation data.
This is an equivalence, not a probability bound.
TEXLINE: main.tex:1207-1239,1392-1421 -/
theorem conditional_phase_execution_abort_iff (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (pref : List Bool) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let mass := (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ¬ ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ t
    mass ≤ 3 / (32 * ((s.L : ENNReal) + 1)) ↔
      mass * (32 * ((s.L : ENNReal) + 1)) ≤ 3 := by
  dsimp only
  exact ENNReal.le_div_iff_mul_le
    (Or.inr (by norm_num : (3 : ENNReal) ≠ 0))
    (Or.inr (by norm_num : (3 : ENNReal) ≠ ⊤))

end CountingMatroid.Analysis.FinitePhaseExecutionAbort

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r22 · rejected handoff · `r22-conditional-abort-mse-1` was mechanically
  rejected without diagnostic. The attempted Option-output expansion isolates
  actual restart and observation aborts. Phase zero has no restart failure,
  but capped draws remain; positive phases require the uncapped return-time
  expectation, capped-draw law and finite-block coverage. Retained the proved
  normalization and kept the estimate local to the assigned parent.
-/
