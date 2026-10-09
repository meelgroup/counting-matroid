import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.SuccessfulPrefixCursor
import CountingMatroid.Analysis.BoundedUniformAbortMass

set_option autoImplicit false

/-!
The operational certificate still needed for a positive phase restart.
It separates an underlying-transition cost with the paper's expected budget
from covered, prefix-free histories of the actual capped integer calls.
The consuming theorem supplies finite Markov and union bounds; the sampling
law is proved in BoundedUniformAbortMass. No expectation or coverage claim
is assumed by these definitions.
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
  obtain ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, hprefLength⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor
      n r o₁ o₂ p j hj pref hprefix
  -- BLOCKER: instrument the actual capped restart to retain its underlying
  -- attempt count on abort, and construct its ordinal draw-site histories.
  -- Bound that stopped cost by the uncapped warm-restart expectation
  -- 20*n²*L*τ. No trace-excursion law or warm-stage mixing bridge is yet
  -- available; the actual finite tape also needs denominator-width coverage.
  -- A second route through Arlib.MarkovChains.EHT does not give this
  -- positive-time return cost: EHT_eq_zero_of_mem is zero when starting
  -- in the target, while a checked n=0/cap=1/lazy probe of traceReturn
  -- increments attempts to one. One needs a one-step excursion expression,
  -- hitting summability, and its operational-law bridge before using EHT.
  -- The proved successful-prefix good-cursor extraction is in downstream
  -- SuccessfulPrefixAbortBound, which imports the parent; it cannot be
  -- imported here without moving those two extraction lemmas to a lower file.
  -- The positive-denominator rejection law and adaptive prefix transfer are
  -- already proved in BoundedUniformAbortMass, not assumptions here.
  /- PARKED: The saturated-cost route below proves the deterministic cover
  but cannot supply the moment: its mean is restartCap, rather than the
  paper's much smaller 20*n²*L*τ. Lean stopped at line 58 with
  `error: not a positivity goal`. Use an actual stopped-cost instrument;
  this constant witness is not a draft to patch.
  classical
  dsimp only
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let emptyDraw : BoundedUniformAbortMass.DrawHistory pref t s.drawTrials :=
    ⟨∅, fun _ => 1, by simp, by simp, by simp, by simp⟩
  refine ⟨(fun _ => s.restartCap), (fun _ => emptyDraw), ?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, card_vector,
      Fintype.card_bool, nsmul_eq_mul]
    push_cast
    positivity
  · intro suffix _
    exact Or.inl le_rfl

  -/
  sorry

end CountingMatroid.Analysis.RestartCostDrawCover

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · blocked · live handoff `restart_cost_cover_r26_wave1` was mechanically rejected without further diagnostic; ownership remains here. A checked probe separates zero-time EHT from the actual positive-time trace return. The stopped-cost moment and finite draw-site construction remain the only open proof.

* r26 · handoff-ready · separated the actual transition-cost moment and covered draw-history construction from the proved finite Markov/union reduction. A saturated cap cost proves the deterministic cover, but its moment is too large; the instrumented stopped cost and its uncapped expectation remain open.
-/
