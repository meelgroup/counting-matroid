import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List
import CountingMatroid.Analysis.RatioProductAccuracy
import CountingMatroid.Analysis.FiniteTapePhaseControl
import CountingMatroid.Analysis.BoundedRunPhaseHistory
import CountingMatroid.Analysis.BoundedRunResourceEnvelope
import CountingMatroid.Analysis.FirstPhaseFailure
import CountingMatroid.Analysis.FiniteTapeFirstPhaseBound
import CountingMatroid.Analysis.FiniteTapePrefixBound
import CountingMatroid.Analysis.CertifiedPhaseRatioSteps
import CountingMatroid.Analysis.SuccessfulPhaseReplay
import CountingMatroid.Analysis.ObservePhaseIntervalReplay
import CountingMatroid.Analysis.RestartPhaseIntervalReplay
import CountingMatroid.Analysis.SinglePhaseIntervalReplay
import CountingMatroid.Analysis.PhaseMeanCertificate
import Mathlib.Data.Set.Card.Arithmetic
import CountingMatroid.Analysis.FinitePhaseEstimationBound
import CountingMatroid.Analysis.FinitePhaseObservationMSE
import CountingMatroid.Analysis.FinitePhaseExecutionAbort
import CountingMatroid.Analysis.SuccessfulPrefixAbortBound
import CountingMatroid.Analysis.SuccessfulPrefixObservationMSE

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapeLowerTail

open CountingMatroid.Model

/-- INTERNAL: Specialize the proved telescoping estimate to an accurate-ratio
witness for the actual run. This implication also excludes zero-output tapes;
it requires neither exact oracles nor a separate nonzero-output hypothesis.
TEXLINE: main.tex:1290-1311 -/
theorem accurateRatioProduct_lower_bound (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (tape : ℕ → Bool)
    (h : FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p tape) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    (1 - p.ε / 4) * TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ s.L) ≤
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
  have hρ : 0 < s.ρ := by
    change 0 < 1 - 1 / ((2 * n : ℕ) : ℚ)
    push_cast
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    apply sub_pos.mpr
    apply (div_lt_one (by positivity : (0 : ℚ) < 2 * n)).mpr
    linarith
  have hη : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
    change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
    push_cast
    rfl
  have hC : ∀ j, 0 < C j := by
    intro j
    apply Finset.sum_pos
    · intro A _
      exact pow_pos (pow_pos hρ j) _
    · exact Finset.univ_nonempty
  have hCzero : C 0 = (2 : ℚ) ^ n := by
    simp [C, TransversalPartition.partitionSum]
  obtain ⟨R, hout, hR⟩ := h
  have hratios : ∀ j < s.L,
      (1 - p.ε / (32 * ((s.L : ℚ) + 1))) /
        (1 + p.ε / (32 * ((s.L : ℚ) + 1))) ≤ R j / (C (j + 1) / C j) ∧
      R j / (C (j + 1) / C j) ≤
        (1 + p.ε / (32 * ((s.L : ℚ) + 1))) /
          (1 - p.ε / (32 * ((s.L : ℚ) + 1))) := by
    simpa only [← hη] using hR
  have hp := (RatioProductAccuracy.ratio_product_accuracy s.L p.ε C R
    p.ε_pos p.ε_lt_one hC hratios).1
  rw [hCzero] at hp
  simpa only [hout] using hp

/-- INTERNAL: Every lower-tail tape fails the accurate-ratio invariant,
including tapes on which the bounded run aborts. The finite-cardinality
comparison does not condition on the run returning a nonzero value.
TEXLINE: main.tex:1287-1311,1392-1427 -/
theorem lower_tail_mass_le_ratio_failure (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let c := TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ s.L)
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s < (1 - p.ε / 4) * c} : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤
      (Set.ncard {bits : List Bool | bits.length = m ∧
        ¬ FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p
          (fun i => (bits[i]?).getD false)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let c := TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ s.L)
  let low : Set (List Bool) := {bits | bits.length = m ∧
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
      (fun i => (bits[i]?).getD false) s < (1 - p.ε / 4) * c}
  let failed : Set (List Bool) := {bits | bits.length = m ∧
    ¬ FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p
      (fun i => (bits[i]?).getD false)}
  have hsubset : low ⊆ failed := by
    intro bits hb
    refine ⟨hb.1, ?_⟩
    intro haccurate
    exact (not_lt_of_ge (accurateRatioProduct_lower_bound n r o₁ o₂ p hn
      (fun i => (bits[i]?).getD false) haccurate)) hb.2
  have hfinite : failed.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : low.ncard ≤ failed.ncard := Set.ncard_le_ncard hsubset hfinite
  change (low.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
    (failed.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m
  gcongr

/-- INTERNAL: Convert the proved history-product witness to the existing
accurate-ratio predicate, evaluating only the program's final power-of-two
scale. The history module itself need not depend on phase-control analysis.
TEXLINE: main.tex:1202-1205,1290-1304 -/
private theorem phase_history_accurate (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (hgood : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      BoundedRunPhaseHistory.PhaseRatioStep r o₁ o₂ p tape j) :
    FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p tape := by
  obtain ⟨R, ⟨current, hc, hp⟩, hR⟩ :=
    BoundedRunPhaseHistory.successful_history_product r o₁ o₂ p tape hgood
  refine ⟨R, ?_, hR⟩
  rw [BoundedRunPhaseHistory.singleRun_eq_phaseHistory, hc]
  change ((CountingMatroid.Program.natPower 2 n).val : ℚ) * current.product = _
  rw [BoundedRunResourceEnvelope.natPower_value, hp]
  push_cast
  rfl

/-- INTERNAL: Cover failed global ratio witnesses by the first unsuccessful
phase of the actual bounded-run fold. The phase-history representation
retains aborts and imposes no nonzero-output guard.
TEXLINE: main.tex:1273-1304 -/
theorem ratio_failure_mass_le_first_phase_failure (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      ¬ FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p
        (fun i => (bits[i]?).getD false)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤
      (Set.ncard {bits : List Bool | bits.length = m ∧
        BoundedRunPhaseHistory.FirstPhaseRatioFailure r o₁ o₂ p
          (fun i => (bits[i]?).getD false)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m := by
  let m := CountingMatroid.Model.Run.blockLength n r p
  let failed : Set (List Bool) := {bits | bits.length = m ∧
    ¬ FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p
      (fun i => (bits[i]?).getD false)}
  let firstFailed : Set (List Bool) := {bits | bits.length = m ∧
    BoundedRunPhaseHistory.FirstPhaseRatioFailure r o₁ o₂ p
      (fun i => (bits[i]?).getD false)}
  have hsubset : failed ⊆ firstFailed := by
    intro bits hb
    refine ⟨hb.1, BoundedRunPhaseHistory.first_phase_failure_of_unsuccessful_history
      r o₁ o₂ p (fun i => (bits[i]?).getD false) ?_⟩
    intro hgood
    exact hb.2 (phase_history_accurate n r o₁ o₂ p
      (fun i => (bits[i]?).getD false) hgood)
  have hfinite : firstFailed.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : failed.ncard ≤ firstFailed.ncard :=
    Set.ncard_le_ncard hsubset hfinite
  change (failed.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
    (firstFailed.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m
  gcongr

/-- INTERNAL: Cover first ratio failures by the union of first failures of
the stronger phase certificates, then apply the finite-cardinality union
bound. The certificates carry the good stored multipliers needed by the
upstream conditional probability estimate.
TEXLINE: main.tex:1207-1285 -/
theorem first_ratio_failure_mass_le_certificate_sum (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      BoundedRunPhaseHistory.FirstPhaseRatioFailure r o₁ o₂ p
        (fun i => (bits[i]?).getD false)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤
    ∑ j ∈ Finset.range s.L,
      (Set.ncard {bits : List Bool | bits.length = m ∧
        FirstPhaseFailure.FirstFailure r o₁ o₂
          (fun i => (bits[i]?).getD false) s j} : ENNReal) *
        (1 / 2 : ENNReal) ^ m := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let firstRatio : Set (List Bool) := {bits | bits.length = m ∧
    BoundedRunPhaseHistory.FirstPhaseRatioFailure r o₁ o₂ p
      (fun i => (bits[i]?).getD false)}
  let uncertified : Set (List Bool) := {bits | bits.length = m ∧
    ¬ ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  let failed := fun j => {bits : List Bool | bits.length = m ∧
    FirstPhaseFailure.FirstFailure r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have hsubset : firstRatio ⊆ uncertified := by
    intro bits hb
    refine ⟨hb.1, ?_⟩
    intro hcert
    obtain ⟨j, hj, _, hjbad⟩ := hb.2
    exact hjbad (CertifiedPhaseRatioSteps.certified_phases_ratio_steps
      r o₁ o₂ p hn (fun i => (bits[i]?).getD false) hcert j hj)
  have hfinite : uncertified.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : firstRatio.ncard ≤ ∑ j ∈ Finset.range s.L, (failed j).ncard :=
    (Set.ncard_le_ncard hsubset hfinite).trans
      (FirstPhaseFailure.uncertified_card_le_sum n r o₁ o₂ s m)
  change (firstRatio.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
    ∑ j ∈ Finset.range s.L, ((failed j).ncard : ENNReal) *
      (1 / 2 : ENNReal) ^ m
  calc
    (firstRatio.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        ((∑ j ∈ Finset.range s.L, (failed j).ncard : ℕ) : ENNReal) *
          (1 / 2 : ENNReal) ^ m := by
      gcongr
    _ = _ := by simp only [Nat.cast_sum, Finset.sum_mul]

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

/-- INTERNAL: A one-sided finite-tape form of the paper's successful-phase
product lower bound, including aborted runs. Deterministic history replay,
prefix conditioning, mean-to-certificate containment and the final union bound
are proved. The conditional raw failure is split into execution aborts and
completed observation errors. `FinitePhaseEstimationBound` proves the finite
Markov/observable-union reduction, including schedule arithmetic and the
operational stationary-mean lower bound. The two quantitative obligations are
stated in `SuccessfulPrefixAbortBound` and `SuccessfulPrefixObservationMSE`,
with the actual successful-prefix hypothesis and all original input promises.
Those estimates remain open; the parent applies them explicitly. Both live
handoffs were mechanically rejected, so this remains an unfinished proof with
two exported quantitative obligations, not a completed parallel handoff.
TEXLINE: main.tex:1253-1315,1392-1421 -/
theorem finite_tape_lower_tail_bound (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let c := CountingMatroid.Analysis.TransversalPartition.partitionSum
      r o₁ o₂ (s.ρ ^ s.L)
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s < (1 - p.ε / 4) * c} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  have hsingle : ∀ a (tape : ℕ → Bool)
      (previous next : CountingMatroid.Program.AnnealingCursor n),
      (BoundedRunPhase.boundedRunPhase r o₁ o₂ tape
        (CountingMatroid.Interface.Pseudocode.setup n p) a (some previous)).val = some next →
      previous.bitCursor ≤ next.bitCursor ∧
        ∀ otherTape : ℕ → Bool,
          (∀ i, previous.bitCursor ≤ i → i < next.bitCursor → tape i = otherTape i) →
          (BoundedRunPhase.boundedRunPhase r o₁ o₂ otherTape
            (CountingMatroid.Interface.Pseudocode.setup n p) a (some previous)).val = some next := by
    exact SinglePhaseIntervalReplay.single_phase_interval_replay r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p)
  apply (lower_tail_mass_le_ratio_failure n r o₁ o₂ p hn).trans
  apply (ratio_failure_mass_le_first_phase_failure n r o₁ o₂ p).trans
  apply (first_ratio_failure_mass_le_certificate_sum n r o₁ o₂ p hn).trans
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  calc
    (∑ j ∈ Finset.range s.L,
      (Set.ncard {bits : List Bool | bits.length = m ∧
        FirstPhaseFailure.FirstFailure r o₁ o₂
          (fun i => (bits[i]?).getD false) s j} : ENNReal) *
        (1 / 2 : ENNReal) ^ m) ≤
      ∑ j ∈ Finset.range s.L, (1 / (8 * ((s.L : ENNReal) + 1))) := by
        apply Finset.sum_le_sum
        intro j hj
        apply (FiniteTapeFirstPhaseBound.finite_tape_first_phase_failure_iff
          n r o₁ o₂ p j).mpr
        classical
        let E := fun bits : List Bool => FirstPhaseFailure.FirstFailure r o₁ o₂
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
          let bad : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
            E (pref ++ suffix)}
          let rawBad : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
            (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
              (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
            ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
              (fun i => ((pref ++ suffix)[i]?).getD false) s j}
          have hη : 0 ≤ s.η := by
            change 0 ≤ p.ε / ((32 * (s.L + 1) : ℕ) : ℚ)
            exact div_nonneg p.ε_pos.le (Nat.cast_nonneg _)
          have hηsmall : s.η ≤ (1 / 3 : ℚ) := by
            have hformula : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
              change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
              push_cast
              rfl
            rw [hformula]
            apply (div_le_iff₀ (by positivity : (0 : ℚ) < 32 * ((s.L : ℚ) + 1))).mpr
            have hL : (0 : ℚ) ≤ s.L := Nat.cast_nonneg _
            linarith [p.ε_lt_one]
          have hsubset : bad ⊆ rawBad := by
            intro suffix hb
            refine ⟨hb.1, hb.2.1, ?_⟩
            intro hraw
            exact hb.2.2 (EmpiricalPhaseCertificate.raw_phase_certified r o₁ o₂ _ s j
              hη hηsmall (PhaseMeanCertificate.raw_phase_means_estimates
                n r o₁ o₂ p hn _ j hraw))
          have hfiniteRaw : rawBad.Finite :=
            (List.finite_length_eq Bool (m - pref.length)).subset (fun _ hb => hb.1)
          have hcard : (bad.ncard : ENNReal) ≤ (rawBad.ncard : ENNReal) := by
            exact_mod_cast Set.ncard_le_ncard hsubset hfiniteRaw
          apply (mul_le_mul_of_nonneg_right hcard (by positivity :
            (0 : ENNReal) ≤ (1 / 2 : ENNReal) ^ (m - pref.length))).trans
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
              j (Finset.mem_range.mp hj) pref hprefix
          have hmoment : ∀ index : PhaseObservationExperiment.Observable n,
              (∑ suffix : List.Vector Bool (m - pref.length),
                PhaseObservationExperiment.observationSquaredError r o₁ o₂
                  (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
                (2 : ℚ) ^ (m - pref.length) ≤
                  40000 * (n : ℚ) ^ 8 / s.observations := by
            intro index
            exact SuccessfulPrefixObservationMSE.conditional_successful_prefix_observation_mse
              n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
              j (Finset.mem_range.mp hj) pref hprefix index
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

        have hmass := FiniteTapePrefixBound.finite_prefix_failure_bound
          m P E (1 / (8 * ((s.L : ENNReal) + 1)))
          hlen hfree hcover hconditional
        exact (FiniteTapeFirstPhaseBound.finite_tape_first_phase_failure_iff
          n r o₁ o₂ p j).mp hmass
    _ ≤ (1 / 8 : ENNReal) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      calc
        (s.L : ENNReal) * (1 / (8 * ((s.L : ENNReal) + 1))) ≤
            ((s.L : ENNReal) + 1) * (1 / (8 * ((s.L : ENNReal) + 1))) := by
          gcongr
          exact le_add_right le_rfl
        _ = 1 / 8 := by
          have hz : (s.L : ENNReal) + 1 ≠ 0 := by positivity
          have ht : (s.L : ENNReal) + 1 ≠ ⊤ := by simp
          rw [div_eq_mul_inv, one_mul, ENNReal.mul_inv (Or.inr ht) (Or.inr hz), mul_left_comm,
            ENNReal.mul_inv_cancel hz ht, mul_one]
          simp only [div_eq_mul_inv, one_mul]

end CountingMatroid.Analysis.FiniteTapeLowerTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r23 · genuine blocker · updated live request
  `r23-prefix-cursor-completed-moment-2` was also mechanically rejected
  without compiler diagnostic. Both quantitative children remain owned here
  and open. The target elaborates, but is not proved outright: it still
  depends on restart/draw coupling and warm correlated-observation estimates.

* r23 · blocker · live request `r23-successful-prefix-abort-and-mse-1`
  was mechanically rejected without diagnostic. Retained ownership; proved
  the reached good cursor and exact truncated-prefix length, and restricted
  the masked fair-suffix expectation to completed outputs. Two quantitative
  children still contain the original probability debt; no handoff accepted.

* r23 · parallel boundary · exposed the conditional abort and masked-MSE
  estimates in separate files with all matroid promises and the actual
  successful-prefix hypothesis. Proved completion-failure characterization,
  constructed the real fair suffix law, and identified its exact masked
  moment. The parent applies both open estimates; this is proof debt pending
  live handoff, not outright closure.

* r22 · rejected handoff · `r22-conditional-abort-mse-1` was mechanically
  rejected without diagnostic. Retained all proved observation, mean and
  Markov reductions; replaced the unproved exported estimates with proved
  normalization equivalences and kept both stochastic obligations local.

* r22 · decomposed · defined the actual phase observation experiment, proved
  raw-mean equivalence, stationary mean lower bounds, finite Markov/observable
  union bounds and the schedule estimation budget. The parent separates abort
  mass from masked observation MSE and uses both quantitative children.

* r21 · partial · proved and used rejection-draw, chain-step, capped-return,
  observation, restart, and full-phase interval replay, including monotone
  cursors. The operational hsingle gap is closed; only the conditional
  fresh-suffix raw-mean failure estimate remains; the mean-to-certificate
  containment uses the newly proved stationary-mean and learned-weight bridges.
  The restart handoff was rejected
  without diagnostic, so its proof was completed locally.

* r20 · rejected handoff · `r20-successful-phase-replay-1` was mechanically rejected without diagnostic. Retained ownership and replaced the open replay child by a proved history-induction implication; single-phase operational replay and the conditional suffix estimate remain explicit local obligations of the unchanged target.

* r20 · recovery decomposition · replaced the coupled history-replay/analytic gap with a checked history induction from single-phase interval locality and monotonicity in `SuccessfulPhaseReplay`, plus the unchanged conditional suffix-failure estimate. Proved finite-list consumed-prefix agreement; no target statement or existing import changed.

* r19 · partial · proved fixed-prefix fresh-suffix mass, variable-length prefix-free mass and conditional counting transfer in `FiniteTapePrefixBound`; the parent now uses these facts with the actual successful-history prefix set. Covered length and event containment and the phase-zero prefix case check. The single open obligation is positive-history cursor replay together with the uniform conditional phase estimate; no unproved child exported.

* r18 · rejected handoff · the live first-phase-budget request was mechanically rejected without diagnostic. Retained all proved operational/certificate/counting bridges, and kept the single normalized per-phase probability obligation inside the assigned target; no new unproved exported helper remains.

* r18 · decomposed · combined the proved operational ratio/certificate bridges with `FirstPhaseFailure.uncertified_card_le_sum`; the target now uses the independently stated per-phase probability budget in `FiniteTapeFirstPhaseBound`. That child remains open for live handoff, so this is a verified decomposition rather than outright closure.

* r18 · partial · proved an operational phase-history bridge in `BoundedRunPhaseHistory` and the local `ratio_failure_mass_le_first_phase_failure`; the target now reduces to actual first phase failures, retaining aborts. Conditional phase estimates need the stronger good-multiplier invariant and adaptive finite-tape coupling; no new unproved declaration.

* r17 · partial · proved `accurateRatioProduct_lower_bound` and `lower_tail_mass_le_ratio_failure`; the target now reduces to the unguarded accurate-ratio failure mass. The joint phase law and finite-tape coupling remain open locally; no unproved child was introduced.

* r16 · blocked · a fresh direct application of `finite_tape_product_accuracy` fails on the nonzero-output guard; `FeasibilityContract.bounded` is a cost certificate, and source inspection still finds no joint phase-failure and finite-tape coupling estimate. No new declarations or proof debt introduced.
* r15 · blocked · `exact?` found no proof and applying `finite_tape_product_accuracy` failed on its nonzero-output guard; checked the paper's joint 3/32 failure route, whose conditional phase law and bounded finite-tape coupling are absent from the project.
* r14 · open · isolated the positive-ground lower-tail event including aborts; `aesop` and `exact?` cannot supply the conditional phase law or finite-tape coupling.
-/
