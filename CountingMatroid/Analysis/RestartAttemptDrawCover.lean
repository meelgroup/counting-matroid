import CountingMatroid.Analysis.RestartAttemptAccounting
import CountingMatroid.Analysis.SuccessfulPhaseReplay
import CountingMatroid.Analysis.SinglePhaseIntervalReplay
import CountingMatroid.Analysis.ChainDrawAbortAttribution
import CountingMatroid.Analysis.RestartPhaseBitCoverage
import CountingMatroid.Analysis.RestartAttemptDrawSites

set_option autoImplicit false

/-!
Deterministic half of the restart cost certificate. Continuations retain the
same earlier cursor and tables, even when the earlier consumed prefix was
truncated to the block length. The finite prefix-free packaging is proved
from partial stopping descriptors. The operational ordinal-site construction
and abort-path trial coverage remain in RestartAttemptDrawSites. This file
does not assert an expected transition bound.
-/
namespace CountingMatroid.Analysis.RestartAttemptDrawCover

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: Every suffix completion of a consumed successful prefix has
exactly the same reached cursor. The overrun case is a singleton full tape,
so this lemma does not assume finite-block coverage.
TEXLINE: main.tex:1207-1212 -/
theorem continuation_history_eq {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref)
    (suffix : List Bool)
    (hlen : suffix.length = CountingMatroid.Model.Run.blockLength n r p - pref.length) :
    BoundedRunPhaseHistory.phaseHistory r o₁ o₂
      (fun i => ((pref ++ suffix)[i]?).getD false)
      (CountingMatroid.Interface.Pseudocode.setup n p) j = some history.current := by
  let m := CountingMatroid.Model.Run.blockLength n r p
  by_cases hwithin : history.current.bitCursor ≤ m
  · apply SuccessfulPhaseReplay.successful_history_replay_of_phase_replay r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p)
      (SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ _)
      (fun i => (history.bits[i]?).getD false) j history.current history.reached
    intro i hi
    have hipref : i < pref.length := by
      rw [history.consumed, List.length_take, history.length,
        Nat.min_eq_left hwithin]
      exact hi
    rw [List.getElem?_append_left hipref]
    conv_rhs => rw [history.consumed, List.getElem?_take_of_lt hi]
  · have hpref : pref = history.bits := by
      exact history.consumed.trans (List.take_of_length_le (by
        rw [history.length]; exact Nat.le_of_not_ge hwithin))
    have hsuffix : suffix = [] := by
      apply List.length_eq_zero_iff.mp
      rw [hlen, hpref, history.length, Nat.sub_self]
    simpa only [hpref, hsuffix, List.append_nil] using history.reached

/-- INTERNAL: Construct covered prefix-free histories for the at most three
integer calls in each attempted transition of this fixed reached restart.
This is solely an operational abort cover for the instrumented cost.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_attempt_draw_cover (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ draws : Fin (3 * s.restartCap) →
        BoundedUniformAbortMass.DrawHistory pref t s.drawTrials,
      ∀ suffix : List Bool, suffix.length = t →
        (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
          s history.current.tables j history.current.bitCursor).val = none →
        s.restartCap ≤ prefixAttemptCost history suffix ∨
          ∃ k, (draws k).abortEvent suffix := by
  classical
  dsimp only
  obtain ⟨sites, hattribute⟩ :=
    RestartAttemptDrawSites.restart_attempt_draw_sites n r o₁ o₂ p hn j hj pref history
  choose draws hdraws using fun k =>
    StoppedDrawHistory.stopped_draw_history pref
      (CountingMatroid.Model.Run.blockLength n r p - pref.length)
      (CountingMatroid.Interface.Pseudocode.setup n p).drawTrials (sites k)
  refine ⟨draws, ?_⟩
  intro suffix hlen habort
  have hcounted :
      (countedRestart r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
        j history.current.bitCursor).val.1 = none := by
    rw [countedRestart_projection]
    exact habort
  rcases hattribute suffix hlen hcounted with hcap | ⟨k, head, v, hsite, hfail⟩
  · exact Or.inl hcap
  · obtain ⟨hm, hd, hp⟩ := hdraws k suffix head v hlen hsite
    refine Or.inr ⟨k, head, hm, hp, ?_⟩
    rw [hd]
    exact hfail

end CountingMatroid.Analysis.RestartAttemptDrawCover

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · replaced the parked existential construction with proved generic stopping-prefix packaging and a separate operational ordinal-site child; parent proof is closed relative to that open child, whose phase-zero branch is proved.

* 2026-10-09 · reduced · proved fixed-history replay for every suffix; separated the ordinal capped-draw cover from expectation, tied to the proved value-preserving restart instrument. Successful endpoint coverage excludes the required draw-abort case.
-/
