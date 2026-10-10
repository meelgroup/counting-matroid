import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.SuccessfulPrefixCursor
import CountingMatroid.Analysis.BoundedUniformAbortMass

import CountingMatroid.Analysis.RestartAttemptMoment
import CountingMatroid.Analysis.RestartAttemptDrawCover

set_option autoImplicit false

/-!
The operational certificate for a positive phase restart is assembled from a
fixed stopped attempt counter and covered ordinal draw histories. The counter
is proved to preserve the actual restart value and to retain attempts on abort.
The expectation and draw-history construction remain separate open children;
this parent selects no synthetic cost and assumes neither claim. Its original
statement and imports are preserved.
-/

namespace CountingMatroid.Analysis.RestartCostDrawCover

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Construct the operational cost and capped-draw stopping histories
needed by the restart Markov argument. The moment is the paper's restart mean;
the cover retains the actual certified history, restart and finite tape.
TEXLINE: main.tex:1207-1239,1392-1421 -/
theorem restart_cost_draw_cover (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hjpos : 0 < j)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ (cost : List Bool → ℕ)
      (draws : Fin (3 * s.restartCap) →
        BoundedUniformAbortMass.DrawHistory pref t s.drawTrials),
      (∑ bits : List.Vector Bool t, (cost bits.val : ℚ)) / (2 : ℚ) ^ t ≤
        20 * (n : ℚ) ^ 2 * (s.L : ℚ) * (s.τ : ℚ) ∧
      ∀ suffix ∈ {suffix : List Bool | suffix.length = t ∧
        (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
        ∃ current : AnnealingCursor n,
          BoundedRunPhaseHistory.phaseHistory r o₁ o₂
            (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = none},
        s.restartCap ≤ cost suffix ∨ ∃ k, (draws k).abortEvent suffix := by
  classical
  obtain ⟨history⟩ := RestartAttemptAccounting.successful_prefix_witness
    n r o₁ o₂ p j hj pref hprefix
  dsimp only
  obtain ⟨draws, hcover⟩ := RestartAttemptDrawCover.restart_attempt_draw_cover
    n r o₁ o₂ p hn j hj pref history
  refine ⟨RestartAttemptAccounting.prefixAttemptCost history, draws,
    RestartAttemptMoment.restart_attempt_moment n r M₁ M₂ o₁ o₂ p hn
      hfull hr h₁ h₂ hpositive j hj pref history, ?_⟩
  intro suffix hsuffix
  obtain ⟨hlen, _, current, hhistory, habort⟩ := hsuffix
  have hfixed := RestartAttemptDrawCover.continuation_history_eq history suffix hlen
  have heq : current = history.current := Option.some.inj (hhistory.symm.trans hfixed)
  subst current
  exact hcover suffix hlen habort

end CountingMatroid.Analysis.RestartCostDrawCover

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · replaced the failed saturated-cost witness with value-preserving stopped attempt accounting; the unchanged parent uses separate fixed-cost moment and ordinal draw-cover children. Same-cursor suffix replay and all accounting projections are proved. The two substantial children retain explicit operational blockers.


* r26 · blocked · live handoff `restart_cost_cover_r26_wave1` was mechanically rejected without further diagnostic; ownership remains here. A checked probe separates zero-time EHT from the actual positive-time trace return. The stopped-cost moment and finite draw-site construction remain the only open proof.

* r26 · handoff-ready · separated the actual transition-cost moment and covered draw-history construction from the proved finite Markov/union reduction. A saturated cap cost proves the deterministic cover, but its moment is too large; the instrumented stopped cost and its uncapped expectation remain open.
-/
