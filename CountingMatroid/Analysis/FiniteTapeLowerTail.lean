import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List
import CountingMatroid.Analysis.RatioProductAccuracy
import CountingMatroid.Analysis.FiniteTapePhaseControl

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

/-- INTERNAL: A one-sided finite-tape form of the paper's successful-phase
product lower bound. Unlike the completed-product error event, this event
includes aborted runs, so it can directly control the zero-output mass.
The deterministic containment is proved; the joint finite-tape failure
probability bound remains open in this declaration.
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
  -- BLOCKER (missing joint finite-tape phase estimate): the remaining goal is
  -- precisely the mass of {bits | bits.length = blockLength n r p ∧
  --   ¬ FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p
  --     (fun i => (bits[i]?).getD false)} ≤ 1/8.
  -- Both deterministic steps are proved above: telescope an accurate witness,
  -- then include the lower-tail event in its complement. No nonzero guard is
  -- needed in either step. The existing `finite_tape_inaccurate_ratios` bounds
  -- only the intersection of this complement with nonzero-output tapes.
  -- Its statement therefore cannot finish this residual goal.
  --
  -- To prove the unguarded estimate, main.tex:1207-1285 gives the uncapped
  -- conditional restart/observation failure budget 1/16; main.tex:1392-1427
  -- adds 1/32 for capped rejection draws. The required operational bridge is
  -- that the actual boundedRun has an accurate witness outside those events,
  -- with every adaptive bit read covered by Run.blockLength. The project has
  -- no such joint phase law/coupling theorem. Markov's inequality requires the
  -- restart mean and observation MSE for this law; unfolding boundedRun exposes
  -- a deterministic repeatFor, not either probabilistic premise. This is a
  -- same-paper proof obligation, not a Prior proposal. The downstream
  -- AbortTapeBound uses this target, so it cannot supply the missing abort mass.

  sorry

end CountingMatroid.Analysis.FiniteTapeLowerTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · partial · proved `accurateRatioProduct_lower_bound` and `lower_tail_mass_le_ratio_failure`; the target now reduces to the unguarded accurate-ratio failure mass. The joint phase law and finite-tape coupling remain open locally; no unproved child was introduced.

* r16 · blocked · a fresh direct application of `finite_tape_product_accuracy` fails on the nonzero-output guard; `FeasibilityContract.bounded` is a cost certificate, and source inspection still finds no joint phase-failure and finite-tape coupling estimate. No new declarations or proof debt introduced.
* r15 · blocked · `exact?` found no proof and applying `finite_tape_product_accuracy` failed on its nonzero-output guard; checked the paper's joint 3/32 failure route, whose conditional phase law and bounded finite-tape coupling are absent from the project.
* r14 · open · isolated the positive-ground lower-tail event including aborts; `aesop` and `exact?` cannot supply the conditional phase law or finite-tape coupling.
-/
