import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapePhaseControl

open CountingMatroid.Model

/-- INTERNAL: A completed run admits empirical phase ratios obeying the
paper's relative ratio bounds and multiplying to its actual output. A proof
from the program should take these ratios from the successive `finishPhase`
results, using the learned tables from the same execution.
TEXLINE: main.tex:1190-1205,1290-1304 -/
def AccurateRatioProduct (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
  ∃ R : ℕ → ℚ,
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
      (2 : ℚ) ^ n * (∏ j ∈ Finset.range s.L, R j) ∧
    ∀ j < s.L,
      (1 - s.η) / (1 + s.η) ≤ R j / (C (j + 1) / C j) ∧
      R j / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η)

/-- INTERNAL: A nonzero capped finite-tape run fails to admit accurate
empirical ratios with probability at most one eighth. The intended witness
is the sequence of `finishPhase` ratios in `Program.boundedRun`.
TEXLINE: main.tex:1207-1296,1392-1427 -/
theorem finite_tape_inaccurate_ratios (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s ≠ 0 ∧
      ¬ AccurateRatioProduct n r o₁ o₂ p
        (fun i => (bits[i]?).getD false)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  -- ATTEMPT: unfolding AccurateRatioProduct, singleRun, boundedRun, and
  -- charged value binds, followed by aesop, leaves the event-mass bound
  -- over the repeatFor phase fold. A separate exact? probe also found no
  -- applicable proof of the probability bound.
  -- BLOCKER: after unfolding the witness and the bounded-run fold, the
  -- missing premise is the conditional law of each actual phase. On a
  -- successful history, the uncapped restart and observations must fail
  -- with probability at most 1/(16*(s.L+1)); accurate observations preserve
  -- the learned-multiplier invariant. Sum over phases, then couple capped
  -- draws and the finite tape to that experiment. The latter also needs
  -- cursor/denominator bounds ensuring all reads lie below blockLength.
  -- Neither a marginal bounded-draw value law nor conditioning chainStep
  -- on no abort suffices: acceptance-draw abort probability depends on
  -- the proposal. The joint value/cursor law and fresh unused suffix are
  -- needed for the adaptive composition. These are same-paper obligations.
  sorry

end CountingMatroid.Analysis.FiniteTapePhaseControl

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · blocked · live handoff admission was mechanically rejected with no further diagnostic; ownership remains here. Both unfolding with `aesop` and direct `exact?` failed on the missing phase probability bound.
* r16 · open · extracted the accurate-ratio witness probability bound; unfolding the actual bounded-run fold and `aesop` leave the conditional phase law and finite-tape coupling. The deterministic product implication is proved separately.
-/
