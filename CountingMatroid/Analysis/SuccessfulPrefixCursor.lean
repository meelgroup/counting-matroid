import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.InitialMultipliersGood

set_option autoImplicit false

namespace CountingMatroid.Analysis.SuccessfulPrefixAbortBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Earlier actual phase certificates supply a reached good cursor
on the same tape, without any replay or tape-coverage assumption.
TEXLINE: main.tex:1207-1212 -/
theorem certified_history_has_good_cursor {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (hprevious : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape
      (CountingMatroid.Interface.Pseudocode.setup n p) a) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    ∃ current : AnnealingCursor n,
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
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
        show BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s a =
          some previous from hpreviousCursor]
      exact hnext

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
  have hcurrent := certified_history_has_good_cursor r o₁ o₂ p
    (fun i => (bits[i]?).getD false) j hj hprevious
  obtain ⟨current, hhistory, hstored⟩ := hcurrent
  change pref = bits.take (match BoundedRunPhaseHistory.phaseHistory r o₁ o₂
    (fun i => (bits[i]?).getD false) s j with
    | none => 0
    | some result => result.bitCursor) at hpref
  rw [hhistory] at hpref
  refine ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, ?_⟩
  rw [hpref, List.length_take, hlen]

end CountingMatroid.Analysis.SuccessfulPrefixAbortBound
