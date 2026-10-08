import CountingMatroid.Analysis.SuccessfulPrefixAbortBound
import CountingMatroid.Analysis.SuccessfulPrefixObservationMSE
import CountingMatroid.Analysis.SuccessfulPhaseReplay
import CountingMatroid.Analysis.SinglePhaseIntervalReplay
import CountingMatroid.Analysis.FiniteTapePrefixBound

set_option autoImplicit false

/-!
Transfer the conditional abort and masked-observation estimates to a whole
finite tape using the prefix-free consumed cursors of successful histories.
No new stochastic assumption is introduced. The analytic bounds are imported
from their existing proof modules.
-/

namespace CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound

open CountingMatroid.Model

/-- INTERNAL: Matching the consumed prefix of a finite tape gives agreement
at every bit below the consumed cursor, provided that cursor is within the
tape. This uses defaulted list indexing, exactly as in singleRun.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem consumed_prefix_tape_agreement (bitsA bitsB : List Bool) (k : ℕ)
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

/-- INTERNAL: Bound failure of the actual raw empirical phase conditions
following certified earlier phases. Successful consumed prefixes partition
these tapes; their conditional abort and completed-error budgets total
1/[8(L+1)], including capped random draws.
TEXLINE: main.tex:1207-1285,1392-1427 -/
theorem finite_tape_raw_phase_failure_bound (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => (bits[i]?).getD false) s a) ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => (bits[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ 1 / (8 * ((s.L : ENNReal) + 1)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  have hsingle := SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂ s
  let E := fun bits : List Bool =>
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
      (fun i => (bits[i]?).getD false) s j
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
    exact ⟨bits, hfinite.mem_toFinset.mpr ⟨hb, he.1⟩, rfl⟩
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
    have hagree := consumed_prefix_tape_agreement bitsA bitsB (cursor bitsA)
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
          r o₁ o₂ s hsingle
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
  have hconditional : ∀ pref ∈ P,
      (Set.ncard {suffix : List Bool |
        suffix.length = m - pref.length ∧ E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤
          1 / (8 * ((s.L : ENNReal) + 1)) := by
    intro pref hp
    let rawBad : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
      E (pref ++ suffix)}
    have hprefix : PhaseObservationExperiment.SuccessfulPhasePrefix
        n r o₁ o₂ p j pref := by
      obtain ⟨bits, hb, hpref⟩ := Finset.mem_image.mp hp
      have hgood := hfinite.mem_toFinset.mp hb
      exact ⟨bits, hgood.1, hgood.2, hpref.symm⟩
    let aborted : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ¬ PhaseObservationExperiment.ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j}
    let inaccurate : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
      PhaseObservationExperiment.ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j}
    have hcoverRaw : rawBad ⊆ aborted ∪ inaccurate := by
      intro suffix hs
      by_cases hdone : PhaseObservationExperiment.ObservationCompleted r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j
      · exact Or.inr ⟨hs.1, hdone, hs.2.2⟩
      · exact Or.inl ⟨hs.1, hs.2.1, hdone⟩
    have hfiniteUnion : (aborted ∪ inaccurate).Finite :=
      (List.finite_length_eq Bool (m - pref.length)).subset (by
        intro suffix hs
        exact hs.elim (fun h => h.1) (fun h => h.1))
    have hrawCard : rawBad.ncard ≤ aborted.ncard + inaccurate.ncard :=
      (Set.ncard_le_ncard hcoverRaw hfiniteUnion).trans
        (Set.ncard_union_le aborted inaccurate)
    have habort : (aborted.ncard : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤
          3 / (32 * ((s.L : ENNReal) + 1)) := by
      exact SuccessfulPrefixAbortBound.conditional_successful_prefix_abort_mass
        n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
        j hj pref hprefix
    have hmoment : ∀ index : PhaseObservationExperiment.Observable n,
        (∑ suffix : List.Vector Bool (m - pref.length),
          PhaseObservationExperiment.observationSquaredError r o₁ o₂
            (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
          (2 : ℚ) ^ (m - pref.length) ≤
            40000 * (n : ℚ) ^ 8 / s.observations := by
      intro index
      exact SuccessfulPrefixObservationMSE.conditional_successful_prefix_observation_mse
        n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
        j hj pref hprefix index
    have hestimate := FinitePhaseEstimationBound.completed_failure_mass_le
      n r o₁ o₂ p hn j pref hmoment
    calc
      (rawBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) ≤
          (aborted.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) +
          (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) := by
        rw [← add_mul, ← Nat.cast_add]
        gcongr
      _ ≤ 3 / (32 * ((s.L : ENNReal) + 1)) +
          1 / (32 * ((s.L : ENNReal) + 1)) := add_le_add habort hestimate
      _ = 1 / (8 * ((s.L : ENNReal) + 1)) := by
        rw [← ENNReal.add_div]
        norm_num only
        rw [show (32 : ENNReal) * ((s.L : ENNReal) + 1) =
          4 * (8 * ((s.L : ENNReal) + 1)) by ring]
        simp only [div_eq_mul_inv, ENNReal.mul_inv
          (Or.inl (by norm_num : (4 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (4 : ENNReal) ≠ ⊤))]
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]
  exact FiniteTapePrefixBound.finite_prefix_failure_bound
    m P E (1 / (8 * ((s.L : ENNReal) + 1))) hlen hfree hcover hconditional

end CountingMatroid.Analysis.FiniteTapeRawPhaseFailureBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · assembled · proved the whole-tape raw-phase failure bound by successful-history interval replay, prefix-free counting, conditional execution-abort mass, and masked observation MSE. The conditional estimates are existing dependencies, with their analytic obligations retained in the original modules.
-/
