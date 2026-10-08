import CountingMatroid.Analysis.FinitePhaseExecutionAbort
import CountingMatroid.Analysis.InitialMultipliersGood

set_option autoImplicit false

/-!
The conditional execution-abort estimate needed for the lower-tail proof.
The completion-failure characterization below is proved. The quantitative
estimate remains open: its concrete events are the actual restart and
observation outputs, rather than an abstract independent phase law.
-/

namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Operational completion can fail only because no observation
output was produced, or because the produced cursor fails the deterministic
good-weight/nonempty-sample checks. No stochastic estimate is asserted.
TEXLINE: main.tex:1163-1187,1207-1266 -/
theorem observation_not_completed_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j : ℕ) :
    ¬ ObservationCompleted r o₁ o₂ tape s j ↔
      phaseObservationData r o₁ o₂ tape s j = none ∨
      ∃ current observed,
        phaseObservationData r o₁ o₂ tape s j = some (current, observed) ∧
        ¬ (FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
          0 < s.observations) := by
  cases hdata : phaseObservationData r o₁ o₂ tape s j with
  | none => simp [ObservationCompleted, hdata]
  | some pair =>
      rcases pair with ⟨current, observed⟩
      simp [ObservationCompleted, hdata]

/-- INTERNAL: A successful consumed prefix comes from an actual reached
cursor with good stored multipliers. The prefix length is the minimum of the
cursor and the block length; this deliberately does not assume tape coverage.
TEXLINE: main.tex:1148-1160,1207-1212 -/
theorem successful_prefix_has_good_cursor (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    ∃ bits : List Bool, ∃ current : AnnealingCursor n,
      bits.length = m ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => (bits[i]?).getD false) s a) ∧
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
      pref = bits.take current.bitCursor ∧
      pref.length = min current.bitCursor m := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  obtain ⟨bits, hlen, hprevious, hpref⟩ := hprefix
  have hcurrent : ∃ current : AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current := by
    cases j with
    | zero =>
        refine ⟨BoundedRunPhaseHistory.initialCursor n s, rfl, ?_⟩
        simp [FirstPhaseFailure.GoodStoredMultipliers,
          BoundedRunPhaseHistory.initialCursor,
          CountingMatroid.Model.Operations.initialWeights,
          CountingMatroid.Model.Operations.allocateLearnedWeights,
          InitialMultipliersGood.initial_ideal_multiplier]
    | succ a =>
        obtain ⟨ratio, _, _, previous, next, hpreviousCursor, hnext, _, _, hgood⟩ :=
          hprevious a (Nat.lt_succ_self a)
        refine ⟨next, ?_, hgood hj⟩
        rw [BoundedRunPhaseHistory.phaseHistory_succ,
          show BoundedRunPhaseHistory.phaseHistory r o₁ o₂
            (fun i => (bits[i]?).getD false) s a = some previous from hpreviousCursor]
        exact hnext
  obtain ⟨current, hhistory, hstored⟩ := hcurrent
  change pref = bits.take (match BoundedRunPhaseHistory.phaseHistory r o₁ o₂
    (fun i => (bits[i]?).getD false) s j with
    | none => 0
    | some result => result.bitCursor) at hpref
  rw [hhistory] at hpref
  refine ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, ?_⟩
  rw [hpref, List.length_take, hlen]

/-- INTERNAL: Bound the abort mass after fixing a consumed prefix of a
successful history. This includes restart-cap exhaustion and all capped
rejection draws, with finite-block coverage proved as part of the estimate.
The draw budget is 1/[16(L+1)] and the restart-tail budget is 1/[32(L+1)].
TEXLINE: main.tex:1207-1239,1392-1421 -/
theorem conditional_successful_prefix_abort_mass (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ¬ ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 3 / (32 * ((s.L : ENNReal) + 1)) := by
  obtain ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, hprefLength⟩ :=
    successful_prefix_has_good_cursor n r o₁ o₂ p j hj pref hprefix
  dsimp only
  simp_rw [observation_not_completed_iff]
  -- Concrete route: the event now separates absence of operational data
  -- from failure of its invariant checks. Successful-prefix replay gives
  -- fixed good tables once cursor coverage is established. For absent data,
  -- observation_data_iff identifies the restart/observation Option outputs.
  -- BLOCKER: construct the uncapped trace law, prove its expected restart
  -- cost ≤20*n²*L*τ, and couple every boundedUniform draw until its cap.
  -- Cursor and denominator-width bounds are needed to justify fresh suffix
  -- bits within blockLength; operational locality alone does not imply them.
  sorry

end CountingMatroid.Analysis.SuccessfulPrefixAbortBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r23 · reduced · proved `successful_prefix_has_good_cursor`, including the exact min(cursor, blockLength) prefix length; extracting fixed good tables does not establish cursor coverage or a restart tail.

* r23 · attempted · rewrote completion failure into absent data or failed invariant checks; restart-return expectation, capped-draw coupling and finite cursor/width coverage remain open.
-/
