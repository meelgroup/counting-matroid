import Mathlib.Data.List.Sort
import Mathlib.Probability.ProbabilityMassFunction.Constructions
import CountingMatroid.Interface.Encoding

set_option autoImplicit false

/-!
# Mathematical answer side of the annealing program

Correspondence ledger (paper location → this file → charged program):
* main.tex:283–293, exact pretest → `pretest` → `Program.preprocess`.
* main.tex:1105–1150, schedule and initial multipliers → `setup`,
  `initialMultipliers` → `Program.schedule`, `Operations.initialWeights`.
* main.tex:746–751, lazy exchange → `chainStep`, `chainStepLaw` →
  `Program.chainStep`; its classification and paired rank are evaluated there.
* main.tex:1163–1176, fresh transversal and capped trace restart →
  `freshTransversal`, `traceReturn`, `restartPhase` → the identically named
  declarations in `Program`.
* main.tex:1177–1187, consecutive observations → `observePhase` →
  `Program.observePhase` (including `Program.recordObservation`).
* main.tex:1188–1201, zero-frequency abort, ratio, multiplier update →
  `finishPhase` → `Program.finishPhase`.
* main.tex:1202–1205, zero on abort and scaled product → `singleRun` →
  `Program.boundedRun`.
* main.tex:1392–1421, capped binary rejection, including `v=1` →
  `boundedDraw` → `Program.boundedUniform`.
* main.tex:1442–1448, independent runs and median → `median`, `estimate`,
  `estimateLaw` → `Program.medianRational`, `Program.estimate`,
  `Model.Run.fairBlocks` and `Model.Run.algorithmLaw`.
* main.tex:226–229 and 699–702, partition sums and transport: analysis only;
  there is no executable pseudocode or program step for them.

There are two algorithm definitions for a reason. The charged program preserves
its sequence of dictionary operations, which is the object of resource analysis;
a sealed dictionary also remembers order and update history, so equal sets can
be different program terms. Correctness compares laws of extensional sets and
therefore uses `Finset` and `PMF` here. In the present Model the charged paired
state itself is already a `Finset`, but its operations and control flow remain
inside `Charged`. The pure answer composition below removes those charges and
uses Mathlib's extensional state and probability notions. The bridge must show
that this composition has the charged program's answer law.

MODEL: `FeasibilityImplementation` is a parameter, not the cited concrete
polynomial matroid-intersection pretest (main.tex:283–289). Consequently the
algorithm is conditional on a missing implementation. The program also has no
proved RAM realization of its arithmetic or bit operations, and no proof that
`Model.Run.blockLength` covers every fair-bit read. These are program-side gaps,
not extra inputs or hypotheses added here. The full mathematical transition is
kept tape-relative; `chainStepLaw` draws from the same finite fair-bit product
used by `Model.Run`, with the same default for an exhausted block.
-/

namespace CountingMatroid.Interface.Pseudocode

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- Exact empty-ground/feasibility dispatch. `none` enters annealing. -/
noncomputable def pretest (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) : Option ℚ :=
  (CountingMatroid.Program.preprocess solver n r o₁ o₂).val

/-- The paper's rational and integral schedule, evaluated by the same formulas
as the charged setup. -/
noncomputable def setup (n : ℕ) (p : InputParams) : AnnealingSchedule :=
  (CountingMatroid.Program.schedule n p).val

/-- Every ordered defect starts with multiplier four. -/
noncomputable def initialMultipliers (n : ℕ) : Multipliers n :=
  (CountingMatroid.Model.Operations.initialWeights n).val

/-- Capped rejection sampling from a fixed fair-bit tape. `none` is abort. -/
noncomputable def boundedDraw (tape : ℕ → Bool) (trials v cursor : ℕ) :
    Option ℕ × ℕ :=
  (CountingMatroid.Program.boundedUniform tape trials v cursor).val

/-- One lazy exchange attempt on the extensional paired state. -/
noncomputable def chainStep {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) : Option (PairedSet n × ℕ) :=
  (CountingMatroid.Program.chainStep r o₁ o₂ tape trials q weights state cursor).val

/-- The finite-bit law of one transition, using the product fair-bit law of
`Model.Run`. The full algorithm samples a block once per run and shares it
across transitions; this marginal uses the same block distribution. -/
noncomputable def chainStepLaw {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n) :
    PMF (Option (PairedSet n × ℕ)) := do
  let bits ← CountingMatroid.Model.Run.fairTape
    (CountingMatroid.Model.Run.blockLength n r p)
  pure (chainStep r o₁ o₂ (fun i => (bits[i]?).getD false)
    (setup n p).drawTrials q weights state 0)

/-- Fresh transversal selected by n successive fair bits. -/
noncomputable def freshTransversal (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    PairedSet n × ℕ :=
  (CountingMatroid.Program.freshTransversal n tape cursor).val

/-- One positive-time return to the transversal class with the phase-global
attempt cap. -/
noncomputable def traceReturn {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : CountingMatroid.Program.RestartCursor n) :
    Option (CountingMatroid.Program.RestartCursor n) :=
  (CountingMatroid.Program.traceReturn r o₁ o₂ tape s q weights start).val

/-- Fresh restart followed by the learned trace kernels from phases 1 to j. -/
noncomputable def restartPhase {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ) :
    Option (PairedSet n × ℕ) :=
  (CountingMatroid.Program.restartPhase r o₁ o₂ tape s tables j cursor).val

/-- One correlated observation trajectory, including its starting state. -/
noncomputable def observePhase {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) :
    Option (CountingMatroid.Program.ObservationCursor n) :=
  (CountingMatroid.Program.observePhase r o₁ o₂ tape s q weights start).val

/-- Abort on any absent type; otherwise calculate the ratio and next weights. -/
noncomputable def finishPhase {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (weights : Multipliers n)
    (observed : CountingMatroid.Program.ObservationCursor n) :
    Option (ℚ × Multipliers n) :=
  (CountingMatroid.Program.finishPhase s j weights observed).val

/-- One capped run, with zero as the answer on every abort branch. -/
noncomputable def singleRun {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) : ℚ :=
  (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1

/-- Rational median used after the odd number of independent runs. -/
noncomputable def median (answers : List ℚ) : ℚ :=
  ((answers.insertionSort (· ≤ ·))[answers.length / 2]?).getD 0

/-- Pure answer composition on already supplied fair-bit streams. The list
order is immaterial to the median; the charged program builds it by cons. -/
noncomputable def estimate (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) : ℚ :=
  match pretest solver n r o₁ o₂ with
  | some answer => answer
  | none =>
      let s := setup n p
      median ((List.range s.repetitions).map fun j =>
        singleRun r o₁ o₂ (tape j) s)

/-- The answer law under fresh independent fair-bit blocks, using precisely
`Model.Run`'s block length and exhausted-block convention. -/
noncomputable def estimateLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) : PMF ℚ := do
  let s := setup n p
  let blocks ← CountingMatroid.Model.Run.fairBlocks s.repetitions
    (CountingMatroid.Model.Run.blockLength n r p)
  pure (estimate solver n r o₁ o₂ p
    (CountingMatroid.Model.Run.blockTape blocks))

end CountingMatroid.Interface.Pseudocode
