import CountingMatroid.Analysis.RestartAttemptAccounting
import CountingMatroid.Analysis.ChainDrawAbortAttribution
import CountingMatroid.Analysis.RestartPhaseBitCoverage
import CountingMatroid.Analysis.StoppedDrawHistory
import CountingMatroid.Analysis.RestartDrawProbe
import CountingMatroid.Analysis.RestartDrawProbeReplay
import CountingMatroid.Analysis.RestartDrawProbeCoverage
import CountingMatroid.Analysis.RestartDrawProbeAbort

set_option autoImplicit false

/-!
Operational boundary for the deterministic restart abort cover. Concrete
sticky ordinal probes are defined in RestartDrawProbe, with exact counted-value
projection, denominator positivity, and post-capture retention proved there.
Relative-prefix packaging is proved below. The parent proof is closed relative
to three separate open operational obligations: RestartDrawProbeReplay,
RestartDrawProbeCoverage, and RestartDrawProbeAbort. These concern only fixed
probe functions and require no finite-prefix enumeration or probabilistic bound.
-/
namespace CountingMatroid.Analysis.RestartAttemptDrawSites

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.StoppedDrawHistory

/-- INTERNAL: Convert an absolute-cursor probe into a relative stopping
descriptor. Prefix construction, the cursor subtraction, and finite trial
coverage are separated from the program-specific probe laws.
TEXLINE: main.tex:1392-1421 -/
theorem stopped_draw_of_absolute_probe (base t trials : ℕ)
    (probe : List Bool → Option (ℕ × ℕ))
    (hpositive : ∀ bits d, bits.length = t → probe bits = some d → 0 < d.2)
    (hlaws : ∀ bits d, bits.length = t → probe bits = some d →
      base ≤ d.1 ∧ d.1 + trials * ((d.2 - 1).log2 + 1) ≤ base + t ∧
      ∀ other, other.length = t → bits.take (d.1 - base) <+: other →
        probe other = some d) :
    ∃ draw : StoppedDraw t trials,
      ∀ bits, draw.site bits =
        (probe bits).map (fun d => (bits.take (d.1 - base), d.2)) := by
  let site := fun bits => (probe bits).map (fun d => (bits.take (d.1 - base), d.2))
  refine ⟨⟨site, ?_, ?_, ?_, ?_⟩, fun _ => rfl⟩
  · intro bits head v hlen hs
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    exact bits.take_prefix _
  · intro bits other head v hlen hother hs hp
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨hbase, hbudget, hreplay⟩ := hlaws bits d hlen hd
    have htake : (bits.take (d.1 - base)).length = d.1 - base := by
      rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
    have heq : other.take (d.1 - base) = bits.take (d.1 - base) := by
      obtain ⟨tail, rfl⟩ := hp
      simpa only [htake] using
        (List.take_left (l₁ := bits.take (d.1 - base)) (l₂ := tail))
    change (probe other).map _ = _
    rw [hreplay other hother hp, Option.map_some, heq]
  · intro bits head v hlen hs
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    exact hpositive bits d hlen hd
  · intro bits head v hlen hs
    obtain ⟨d, hd, he⟩ := Option.map_eq_some_iff.mp hs
    cases he
    obtain ⟨hbase, hbudget, _⟩ := hlaws bits d hlen hd
    rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
    omega

/-- INTERNAL: Ordinal partial draw descriptors for the counted restart.
Descriptors use the concrete sticky probes in RestartDrawProbe. The imported
operational lemmas state their stopping law, full-trial coverage, and attribution.
Only the actual counted result is used for attribution.
This is the operational part of restart_attempt_draw_cover; it contains no
finite-prefix enumeration or prefix-free combinatorics.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_attempt_draw_sites (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ sites : Fin (3 * s.restartCap) → StoppedDraw t s.drawTrials,
      ∀ suffix : List Bool, suffix.length = t →
        (countedRestart r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
          s history.current.tables j history.current.bitCursor).val.1 = none →
        s.restartCap ≤ prefixAttemptCost history suffix ∨
          ∃ k head v, (sites k).site suffix = some (head, v) ∧
            (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
              s.drawTrials v (pref.length + head.length)).val.1 = none := by
  classical
  dsimp only
  by_cases hz : j = 0
  · subst j
    refine ⟨fun _ => ⟨fun _ => none, ?_, ?_, ?_, ?_⟩, ?_⟩
    · intro bits head v hlen hs
      cases hs
    · intro bits other head v hlen hother hs hp
      cases hs
    · intro bits head v hlen hs
      cases hs
    · intro bits head v hlen hs
      cases hs
    · intro suffix hlen habort
      simp only [countedRestart, Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.repeatFor, List.range_zero,
        Arlib.Computation.Charged.val_foldl_nil,
        Arlib.Computation.Charged.val_pure, Option.map_some] at habort
      cases habort
  · let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let tape := fun (suffix : List Bool) (i : ℕ) => ((pref ++ suffix)[i]?).getD false
    let probe := fun (k : Fin (3 * s.restartCap)) (suffix : List Bool) => RestartDrawProbe.restartDrawProbe r o₁ o₂
      (tape suffix) s history.current.tables j history.current.bitCursor k
    let run := fun (suffix : List Bool) => (RestartDrawProbe.probedRestart r o₁ o₂
      (tape suffix) s history.current.tables j history.current.bitCursor
      0 ⟨0, by decide⟩).val.1
    have hprojection (suffix : List Bool) :
        run suffix = (countedRestart r o₁ o₂ (tape suffix) s
          history.current.tables j history.current.bitCursor).val :=
      RestartDrawProbe.probed_restart_projection r o₁ o₂ (tape suffix) s
        history.current.tables j history.current.bitCursor 0 ⟨0, by decide⟩
    have hoperational :
        (∀ (k : Fin (3 * s.restartCap)) bits d, bits.length = t →
          probe k bits = some d →
          pref.length ≤ d.1 ∧
          d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ pref.length + t ∧
          ∀ other, other.length = t → bits.take (d.1 - pref.length) <+: other →
            probe k other = some d) ∧
        (∀ suffix : List Bool, suffix.length = t → (run suffix).1 = none →
          s.restartCap ≤ (run suffix).2 ∨ ∃ k d,
            probe k suffix = some d ∧
            (boundedUniform (tape suffix) s.drawTrials d.2 d.1).val.1 = none) := by
      constructor
      · intro k bits d hlen hd
        have hr := RestartDrawProbeReplay.restart_draw_probe_replay r o₁ o₂
          s history.current.tables j history.current.bitCursor k (tape bits) d hd
        have hb := RestartDrawProbeCoverage.restart_draw_probe_coverage n r o₁ o₂
          p hn j hj pref history (tape bits) k d hd
        have hstart : pref.length ≤ history.current.bitCursor := by
          have he := congrArg List.length history.consumed
          rw [List.length_take] at he
          exact he.le.trans (Nat.min_le_left _ _)
        have hpref : pref.length ≤ CountingMatroid.Model.Run.blockLength n r p := by
          rw [history.consumed, List.length_take, history.length]
          exact Nat.min_le_right _ _
        have hm : pref.length + t = CountingMatroid.Model.Run.blockLength n r p :=
          Nat.add_sub_of_le hpref
        have hbase := hstart.trans hr.1
        refine ⟨hbase, by simpa only [hm] using hb, ?_⟩
        intro other hother hp
        apply hr.2 (tape other)
        intro i hlo hhi
        change ((pref ++ bits)[i]?).getD false = ((pref ++ other)[i]?).getD false
        by_cases hi : i < pref.length
        · rw [List.getElem?_append_left hi, List.getElem?_append_left hi]
        · rw [List.getElem?_append_right (by omega),
            List.getElem?_append_right (by omega)]
          have htake : (bits.take (d.1 - pref.length)).length = d.1 - pref.length := by
            rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
          obtain ⟨tail, he⟩ := hp
          rw [← he, List.getElem?_append_left (by rw [htake]; omega),
            List.getElem?_take_of_lt (by omega)]
      · intro suffix hlen habort
        have hc : (countedRestart r o₁ o₂ (tape suffix) s history.current.tables
            j history.current.bitCursor).val.1 = none := by
          rw [← hprojection]
          exact habort
        have ha := RestartDrawProbeAbort.restart_draw_probe_abort r o₁ o₂
          (tape suffix) s history.current.tables j history.current.bitCursor hn hc
        simpa only [hprojection, probe] using ha
    choose sites hsites using fun k => stopped_draw_of_absolute_probe
      pref.length t s.drawTrials (probe k)
      (fun bits d _ hd => RestartDrawProbe.restartDrawProbe_positive r o₁ o₂
        (tape bits) s history.current.tables j history.current.bitCursor k d hn hd)
      (hoperational.1 k)
    refine ⟨sites, ?_⟩
    intro suffix hlen habort
    have hrun : (run suffix).1 = none := by
      rw [hprojection]
      exact habort
    rcases hoperational.2 suffix hlen hrun with hcap | ⟨k, d, hd, hfail⟩
    · left
      simpa only [hprojection, prefixAttemptCost, run, tape, s] using hcap
    · obtain ⟨hbase, hbudget, _⟩ := hoperational.1 k suffix d hlen hd
      have htake : (suffix.take (d.1 - pref.length)).length = d.1 - pref.length := by
        rw [List.length_take, hlen, Nat.min_eq_left (by omega)]
      right
      refine ⟨k, suffix.take (d.1 - pref.length), d.2, ?_, ?_⟩
      · rw [hsites k suffix, hd, Option.map_some]
      · rw [htake, Nat.add_sub_of_le hbase]
        exact hfail

end CountingMatroid.Analysis.RestartAttemptDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · verified parallel handoff · restart-probe-recovery-20261009-wave1 accepted after Lean semantic-use validation; scheduler owns RestartDrawProbe and the three open operational children, currently queued. Parent statement unchanged and its proof elaborates.

* 2026-10-09 · handoff preparation · parent uses independent concrete-probe replay, abort-path coverage, and attribution children; all quantitative and prefix transport is proved outside those open obligations.

* 2026-10-09 · recovery · fixed concrete ordinal probes with proved value/cost projection, positivity, and post-capture retention; proved absolute-to-relative stopping descriptor transport. The unchanged target retains one open local operational invariant; no new open declaration or handoff.

* 2026-10-09 · decomposed · closed zero stages; isolated positive-stage ordinal stopping descriptors and abort-path trial coverage from the proved finite-prefix packaging.
-/

/- Historical parked route retained as evidence; superseded by the fixed-probe contract above.
/- PARKED: The positive-stage obligation is now ONLY a family of partial
    stopping descriptors, not DrawHistory finsets. A direct unfolding probe
    reduces countedRestart to a stage fold of countedReturn's early-break
    scan; no imported theorem lifts chainDrawSite across either loop.
    Construct an instrument returning each attempted chain start, indexed
    by the retained counter; site 3*a+b calls chainDrawSite at that start.
    Strengthen the loop invariant with current.attempts = retained count,
    non-invalid current.state, and
      current.bitCursor ≤ restartBase + current.attempts * C,
    C = 1 + 3*s.drawTrials*(4*K+n+1).
    chainDrawSite_success_interval supplies pre-draw replay;
    chain_abort_draw_site attributes failures; chain_draw_site_bit_bound
    gives full-trial coverage at each start even on a failing attempt.
    restart_phase_cursor_le_block alone cannot discharge coverage, since
    it requires a successful endpoint. Use the history multiplier bound
    and quartic schedule arithmetic from RestartPhaseBitCoverage, with
    the shared counter bounded at each allowed attempt. Horizon exhaustion
    with no returned transversal must imply count = s.restartCap.
    OPEN epoch 6 permits a live handoff of this operational child. -/
-/

/- Historical fixed-probe contract attempt; replaced by the three imported obligations.
/- PARKED: Recovery fixes the descriptor functions to the concrete
      restartDrawProbe; no existential instrumentation remains to invent.
      Denominator positivity, exact value/cost projection, and relative-prefix
      packaging are proved, as is probed_return_retains (the post-capture
      tape-independent latch). The first missing local fact is pre-capture
      successful-state replay through probedReturn, composed with capture
      at bodySite and the proved post-capture latch.
      ChainStepIntervalReplay.foldl_successReplay applies to an absorbing
      Option cursor; the probe returns a product containing a continuing
      counted state and a sticky Option descriptor. Its final counted state
      can depend on bits AFTER the observed cursor, so replay of that whole
      product is not a valid intermediate assertion.
      Next executable step: induct over countedReturn's List.range scan with
      two cases: descriptor already captured (use probed_return_retains),
      or not captured (carry successful counted cursor replay).
      At each continuing pre-capture state carry attempts = retained count,
      classifier-valid state, and cursor ≤ restartBase + count*C, where
      C = 1 + 3*s.drawTrials*(4*K+n+1). Lift that invariant through the
      transition and stage folds, use chainDrawSite_success_interval at capture
      and chain_draw_site_bit_bound for all future trials of the draw, including
      the failing attempt. For attribution, a non-returning horizon with no
      draw failure must have spent restartCap tokens. These are operational
      invariants, not borrowed facts or evidence that the statement is false.
      FULL epoch 9: no child handoff; this is the original proof debt, localized
      to laws of fixed probes, with no new open helper declaration. -/
-/
