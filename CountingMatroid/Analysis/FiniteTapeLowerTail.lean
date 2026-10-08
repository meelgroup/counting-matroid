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
import Mathlib.Data.Set.Card.Arithmetic

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

/-- INTERNAL: A one-sided finite-tape form of the paper's successful-phase
product lower bound. Unlike the completed-product error event, this event
includes aborted runs, so it can directly control the zero-output mass.
The deterministic containment, actual-history bridge, stronger-certificate
cover and finite union bound are proved. The remaining per-phase probability
estimate remains open inside this theorem. `FiniteTapePrefixBound` proves
the fixed-prefix fresh-suffix law and the prefix-free conditional counting
reduction. The actual stopping-prefix property and conditional analytic
estimate still need proofs; `FiniteTapeFirstPhaseBound` supplies the
denominator-clearing equivalence.
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
        have hphase :
            (0 < j → ∀ bitsA ∈ good, ∀ bitsB ∈ good, cursor bitsA ≤ m →
              bitsA.take (cursor bitsA) <+: bitsB → cursor bitsB = cursor bitsA) ∧
            (∀ pref ∈ P,
              (Set.ncard {suffix : List Bool |
                suffix.length = m - pref.length ∧ E (pref ++ suffix)} : ENNReal) *
                (1 / 2 : ENNReal) ^ (m - pref.length) ≤
                  1 / (8 * ((s.L : ENNReal) + 1))) := by
          -- BLOCKER: the fresh-suffix counting identity and transfer of a
          -- uniform suffix bound are now proved in FiniteTapePrefixBound.
          -- What remains is specific to the actual bounded-run program:
          -- (1) a positive successful phase history must replay to the same
          -- reached cursor when its consumed prefix is unchanged. Induction
          -- with phaseHistory_succ closes j=0, but at j+1 needs successful
          -- boundedRunPhase replay plus monotonicity of the prior bitCursor.
          -- Unfolding that phase requires the corresponding restartPhase
          -- and observePhase replay facts. No such operational invariant
          -- is in the present API. The generic stopping_prefixes_free lemma
          -- handles cursors beyond m by the whole-tape case, so blockLength
          -- coverage is not a separate premise of prefix-freeness.
          -- (2) uniformly for every such successful prefix, its fresh suffix
          -- has first-certificate-failure mass at most 1/(8*(L+1)). This
          -- needs the uncapped restart mean 20*n^2*L*tau, stationary-mean
          -- observation MSE 40000*n^8/observations, preservation of learned
          -- tables, and capped-draw/finite-block coupling. These are
          -- same-paper obligations at main.tex:1207-1285,1392-1427.
          -- The generic counting law does not establish these analytic or
          -- operational hypotheses, and no new unproved child is exported.
          sorry
        have hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b := by
          by_cases hjzero : j = 0
          · exact hfree_zero hjzero
          · apply FiniteTapePrefixBound.stopping_prefixes_free m
              hfinite.toFinset cursor
            · intro bits hb
              exact (hfinite.mem_toFinset.mp hb).1
            · intro bitsA ha bitsB hb
              exact hphase.1 (Nat.pos_of_ne_zero hjzero)
                bitsA (hfinite.mem_toFinset.mp ha)
                bitsB (hfinite.mem_toFinset.mp hb)
        have hmass := FiniteTapePrefixBound.finite_prefix_failure_bound
          m P E (1 / (8 * ((s.L : ENNReal) + 1)))
          hlen hfree hcover hphase.2
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

* r19 · partial · proved fixed-prefix fresh-suffix mass, variable-length prefix-free mass and conditional counting transfer in `FiniteTapePrefixBound`; the parent now uses these facts with the actual successful-history prefix set. Covered length and event containment and the phase-zero prefix case check. The single open obligation is positive-history cursor replay together with the uniform conditional phase estimate; no unproved child exported.

* r18 · rejected handoff · the live first-phase-budget request was mechanically rejected without diagnostic. Retained all proved operational/certificate/counting bridges, and kept the single normalized per-phase probability obligation inside the assigned target; no new unproved exported helper remains.

* r18 · decomposed · combined the proved operational ratio/certificate bridges with `FirstPhaseFailure.uncertified_card_le_sum`; the target now uses the independently stated per-phase probability budget in `FiniteTapeFirstPhaseBound`. That child remains open for live handoff, so this is a verified decomposition rather than outright closure.

* r18 · partial · proved an operational phase-history bridge in `BoundedRunPhaseHistory` and the local `ratio_failure_mass_le_first_phase_failure`; the target now reduces to actual first phase failures, retaining aborts. Conditional phase estimates need the stronger good-multiplier invariant and adaptive finite-tape coupling; no new unproved declaration.

* r17 · partial · proved `accurateRatioProduct_lower_bound` and `lower_tail_mass_le_ratio_failure`; the target now reduces to the unguarded accurate-ratio failure mass. The joint phase law and finite-tape coupling remain open locally; no unproved child was introduced.

* r16 · blocked · a fresh direct application of `finite_tape_product_accuracy` fails on the nonzero-output guard; `FeasibilityContract.bounded` is a cost certificate, and source inspection still finds no joint phase-failure and finite-tape coupling estimate. No new declarations or proof debt introduced.
* r15 · blocked · `exact?` found no proof and applying `finite_tape_product_accuracy` failed on its nonzero-output guard; checked the paper's joint 3/32 failure route, whose conditional phase law and bounded finite-tape coupling are absent from the project.
* r14 · open · isolated the positive-ground lower-tail event including aborts; `aesop` and `exact?` cannot supply the conditional phase law or finite-tape coupling.
-/
