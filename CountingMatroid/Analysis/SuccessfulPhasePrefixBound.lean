import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.FiniteTapePrefixBound
import CountingMatroid.Analysis.SuccessfulPhaseReplay
import CountingMatroid.Analysis.SinglePhaseIntervalReplay

set_option autoImplicit false

/-!
Lift a uniform fresh-suffix estimate after actual successful phase histories
to the full fair finite-tape estimate. Prefix-freeness follows from successful
history replay, including cursors beyond the block. No stochastic estimate
or finite-block coverage is assumed here.
-/

namespace CountingMatroid.Analysis.SuccessfulPhasePrefixBound

open CountingMatroid.Model

/-- INTERNAL: Matching the consumed prefix of a finite tape gives agreement
at every bit below the consumed cursor, provided that cursor is within the
tape. This uses defaulted list indexing, exactly as in singleRun.
TEXLINE: main.tex:1207-1212,1392-1421 -/
private theorem prefix_bits_agree (bitsA bitsB : List Bool) (k : ℕ)
    (hk : k ≤ bitsA.length) (hp : bitsA.take k <+: bitsB) :
    ∀ i < k, (bitsA[i]?).getD false = (bitsB[i]?).getD false := by
  intro i hi
  have hlength : i < (bitsA.take k).length := by
    simp only [List.length_take]
    omega
  have heq := List.prefix_iff_getElem?.mp hp i hlength
  have htake := List.getElem?_eq_getElem hlength
  rw [List.getElem?_take_of_lt hi] at htake
  rw [heq, htake]

/-- INTERNAL: Operational successful histories provide the prefix-free
partition needed to lift a conditional suffix bound for any phase event.
TEXLINE: main.tex:1207-1212,1277-1285,1392-1427 -/
theorem successful_phase_prefix_bound (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ)
    (E : List Bool → Prop) (β : ENNReal)
    (hprevious : ∀ bits, E bits → ∀ a < j,
      FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => (bits[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) a)
    (hconditional : ∀ pref,
      PhaseObservationExperiment.SuccessfulPhasePrefix n r o₁ o₂ p j pref →
      (Set.ncard {suffix : List Bool |
        suffix.length = CountingMatroid.Model.Run.blockLength n r p - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (CountingMatroid.Model.Run.blockLength n r p - pref.length) ≤ β) :
    (Set.ncard {bits : List Bool |
      bits.length = CountingMatroid.Model.Run.blockLength n r p ∧ E bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ CountingMatroid.Model.Run.blockLength n r p ≤ β := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let cursor := fun bits : List Bool =>
    match BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bits[i]?).getD false) s j with
    | none => 0
    | some current => current.bitCursor
  let good : Set (List Bool) := {bits | bits.length = m ∧
    ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a}
  have hfinite : good.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  let P := hfinite.toFinset.image (fun bits => bits.take (cursor bits))
  have hlen : ∀ pref ∈ P, pref.length ≤ m := by
    intro pref hp
    obtain ⟨bits, hb, rfl⟩ := Finset.mem_image.mp hp
    have hb' : bits ∈ good := hfinite.mem_toFinset.mp hb
    simp only [List.length_take, hb'.1]
    exact Nat.min_le_right _ _
  have hcover : ∀ bits, bits.length = m → E bits →
      ∃ pref ∈ P, pref <+: bits := by
    intro bits hb he
    refine ⟨bits.take (cursor bits), ?_, List.take_prefix _ _⟩
    apply Finset.mem_image.mpr
    exact ⟨bits, hfinite.mem_toFinset.mpr ⟨hb, hprevious bits he⟩, rfl⟩
  have hfree_zero : j = 0 →
      ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b := by
    intro hjzero a ha b hb _
    obtain ⟨bitsA, _, rfl⟩ := Finset.mem_image.mp ha
    obtain ⟨bitsB, _, rfl⟩ := Finset.mem_image.mp hb
    simp only [cursor, hjzero, BoundedRunPhaseHistory.phaseHistory,
      Arlib.Computation.Charged.repeatFor, List.range_zero,
      Arlib.Computation.Charged.val_foldl_nil,
      BoundedRunPhaseHistory.initialCursor, List.take_zero]
  have hreplay : ∀ bitsA ∈ good, ∀ bitsB ∈ good, cursor bitsA ≤ m →
      bitsA.take (cursor bitsA) <+: bitsB → cursor bitsB = cursor bitsA := by
    intro bitsA ha bitsB _ hwithin hprefix
    have hagree := prefix_bits_agree bitsA bitsB (cursor bitsA)
      (by simpa only [ha.1] using hwithin) hprefix
    cases hh : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => (bitsA[i]?).getD false) s j with
    | none =>
        -- Earlier certificates prevent an aborted prefix at positive j.
        cases j with
        | zero =>
            change some (BoundedRunPhaseHistory.initialCursor n s) = none at hh
            contradiction
        | succ a =>
            obtain ⟨_, _, _, previous, next, hprevious, hstep, _⟩ := ha.2 a (by omega)
            have hnext : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
                (fun i => (bitsA[i]?).getD false) s (a + 1) = some next := by
              rw [BoundedRunPhaseHistory.phaseHistory_succ]
              change BoundedRunPhaseHistory.phaseHistory r o₁ o₂
                (fun i => (bitsA[i]?).getD false) s a = some previous at hprevious
              rw [hprevious]
              exact hstep
            rw [hh] at hnext
            contradiction
    | some current =>
        have hb := SuccessfulPhaseReplay.successful_history_replay_of_phase_replay
          r o₁ o₂ s
          (SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s)
          (fun i => (bitsA[i]?).getD false) j current hh
          (fun i => (bitsB[i]?).getD false) (by simpa only [cursor, hh] using hagree)
        simp only [cursor, hh, hb]
  have hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b := by
    by_cases hjzero : j = 0
    · exact hfree_zero hjzero
    · apply FiniteTapePrefixBound.stopping_prefixes_free m
        hfinite.toFinset cursor
      · intro bits hb
        exact (hfinite.mem_toFinset.mp hb).1
      · intro bitsA ha bitsB hb
        exact hreplay bitsA (hfinite.mem_toFinset.mp ha)
          bitsB (hfinite.mem_toFinset.mp hb)
  apply FiniteTapePrefixBound.finite_prefix_failure_bound m P E β hlen hfree hcover
  intro pref hp
  apply hconditional pref
  obtain ⟨bits, hb, hpref⟩ := Finset.mem_image.mp hp
  have hgood := hfinite.mem_toFinset.mp hb
  exact ⟨bits, hgood.1, hgood.2, hpref.symm⟩

end CountingMatroid.Analysis.SuccessfulPhasePrefixBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · proved · operational replay supplies prefix-free successful consumed histories, so uniform suffix bounds transfer to the full tape, including truncated cursors.
-/
