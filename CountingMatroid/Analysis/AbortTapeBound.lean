import CountingMatroid.Interface.Pseudocode
import CountingMatroid.Analysis.BoundedRunResourceEnvelope
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.AbortTapeBound

open CountingMatroid.Model
open CountingMatroid.Model.Operations

/-- INTERNAL: The schedule has no phases on an empty ground set.
TEXLINE: main.tex:1105-1150 -/
theorem setup_zero_phases (p : InputParams) :
    (CountingMatroid.Interface.Pseudocode.setup 0 p).L = 0 := by
  unfold CountingMatroid.Interface.Pseudocode.setup CountingMatroid.Program.schedule
  simp only [Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, natMul, natAdd, ratDiv,
    Arlib.Computation.Charged.val_op,
    Arlib.Computation.Charged.val_opMany]
  simp

/-- INTERNAL: A zero-phase run cannot return the abort value.
TEXLINE: main.tex:1202-1205 -/
theorem singleRun_ne_zero_of_zero_phases (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (hL : s.L = 0) :
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s ≠ 0 := by
  change (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 ≠ 0
  rw [CountingMatroid.Analysis.BoundedRunResourceEnvelope.boundedRun_zero_phases_value
    n r o₁ o₂ tape s hL]
  positivity

/-- INTERNAL: At most one eighth of the fair finite tapes make the capped
annealing run return its abort value. This isolates restart, zero-count, and
bounded-draw aborts from inaccurate completed estimates.
TEXLINE: main.tex:1253-1329,1392-1421 -/
theorem abort_tape_mass_bound (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s = 0} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  by_cases hn : n = 0
  · subst n
    have hL := setup_zero_phases p
    have hempty : {bits : List Bool |
        bits.length = CountingMatroid.Model.Run.blockLength 0 r p ∧
        CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false)
          (CountingMatroid.Interface.Pseudocode.setup 0 p) = 0} = ∅ := by
      ext bits
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_and]
      intro _
      exact singleRun_ne_zero_of_zero_phases 0 r o₁ o₂
        (fun i => (bits[i]?).getD false) _ hL
    simp only [hempty, Set.ncard_empty, Nat.cast_zero, zero_mul]
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    -- BLOCKER (main.tex:1202-1280,1392-1421): the paper bounds two events in
    -- an uncapped experiment: an unsuccessful restart or a missing observed
    -- type, and exhaustion of the rejection sampler's trial cap. Neither that
    -- experiment nor a coupling to `Program.boundedRun` exists in the current
    -- analysis. `Program.boundedRun` returns only `(estimate, bitCursor)`, so
    -- unfolding its value cannot identify which abort branch produced zero.
    -- Executable next step: instrument an analysis-only run with a status that
    -- distinguishes restart, zero-type, and bounded-draw aborts. Prove its
    -- estimate equals `Program.boundedRun.val.1` on every tape, then prove that
    -- positive completed ratios exclude zero output. This gives a *cover* of
    -- this exact zero-output event by the three status events. Bound restart and
    -- zero-type statuses using the paper's conditional phase estimates, and
    -- draw status using the trial-cap coupling. Only then apply a finite-tape
    -- union bound. Merely changing the event to `singleRun = 0` under another
    -- name does not reduce the present obligation. In the current source,
    -- `traceReturn` and `observePhase` use `Option` for both draw exhaustion and
    -- other failures, while `boundedRun` further collapses every `none` to zero.
    -- There is no theorem bounding the resulting status events or relating the
    -- uncapped law in main.tex:1202-1280 to this finite-tape execution.
    sorry

end CountingMatroid.Analysis.AbortTapeBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · partial · proved the empty-ground case using the schedule's zero phase count and `boundedRun_zero_phases_value`; the positive-ground tape mass remains open.
* r7 · blocked · source audit found no abort-status cover, uncapped restart law, or finite-tape coupling; direct `rfl` and targeted schedule simplification did not yield even the empty-ground subcase.
* r6 · blocked · `boundedRun` erases abort causes and no uncapped experiment or coupling is formalized; the exact event cover and conditional bounds are specified above.
* r5 · open · direct simplification reduces the claim to an abort-tape count bound; restart and capped-draw estimates for `Program.boundedRun` are missing.
-/
