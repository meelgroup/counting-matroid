import Mathlib.Probability.ProbabilityMassFunction.Constructions
import CountingMatroid.Model.Program
import CountingMatroid.Meta.ModelClosure

set_option autoImplicit false

/-!
# Fair-bit source and law of the charged estimator

Correspondence ledger: main.tex:102–103 and 1392–1421 give the independent
unbiased bits of `fairBitLaw`; `fairTape` and `fairBlocks` recursively generate
fresh bits for each bounded run. The chosen `blockLength` uses the very
`Program.schedule` value used by the charged estimator, so the schedule is not
restated. Its deliberately coarse polynomial width must still be proved to
cover every rational acceptance denominator before the output law can support
the paper's accuracy proof. `algorithmLaw` maps each block to one invocation of
`Program.estimate`; `outputLaw` records the value and the costs of that same
charged execution. Drawing a full product tape here is distribution semantics,
not an instruction to eagerly generate or charge unused bits.
-/

namespace CountingMatroid.Model.Run

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- One independent unbiased Boolean draw. -/
noncomputable def fairBitLaw : PMF Bool :=
  PMF.ofFintype (fun _ : Bool => 1 / 2)
    (by simpa [Fintype.sum_bool, two_mul] using (ENNReal.add_halves (1 : ENNReal)))

/-- A finite product of fresh fair bits, by recursion so the cons case unfolds. -/
noncomputable def fairTape : (m : ℕ) → PMF (List Bool)
  | 0 => pure []
  | m + 1 => do
      let bit ← fairBitLaw
      let rest ← fairTape m
      pure (bit :: rest)

/-- A coarse finite tape block for one run. The budget depends on the actual
schedule declaration; proving sufficient rational width is outstanding. -/
noncomputable def blockLength (n r : ℕ) (p : InputParams) : ℕ :=
  let s := (CountingMatroid.Program.schedule n p).val
  let width := 1000000 * (s.L + 1) ^ 4 * (n + 1) ^ 4 *
    (s.observations + 1) ^ 4 * (binaryInputLength n r p + 1) ^ 4
  n * s.L + s.drawCalls * (1 + s.drawTrials * width) + 10

/-- Fresh, disjoint finite bit blocks for all median repetitions. -/
noncomputable def fairBlocks (m length : ℕ) : PMF (List (List Bool)) :=
  match m with
  | 0 => pure []
  | m + 1 => do
      let block ← fairTape length
      let remaining ← fairBlocks m length
      pure (block :: remaining)

/-- Out-of-range accesses read a deterministic default; the tape-coverage
proof must show the estimator never reaches one on a promised input. -/
def blockTape (blocks : List (List Bool)) (run bit : ℕ) : Bool :=
  ((blocks[run]?).getD [])[bit]?.getD false

/-- Distribution of charged executions of the one program. -/
noncomputable def algorithmLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    PMF (Arlib.Computation.Charged Op Cell ℚ) := do
  let repetitions := (CountingMatroid.Program.schedule n p).val.repetitions
  let blocks ← fairBlocks repetitions (blockLength n r p)
  pure (CountingMatroid.Program.estimate solver n r o₁ o₂ p
    (blockTape blocks))

/-- The rational answer and separate counters are projections of the same
charged execution, including all work on abort paths. -/
noncomputable def outputLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    PMF (ℚ × ExecutionCost) := do
  let run ← algorithmLaw solver n r o₁ o₂ p
  pure (run.val,
    { oracleCalls := oracleCalls run,
      bitOps := otherSteps run,
      randomBits := run.cost Op.fairBit })

end CountingMatroid.Model.Run

#modelClosure CountingMatroid.Model.Run.fairBitLaw
#modelClosure CountingMatroid.Model.Run.fairTape
#modelClosure CountingMatroid.Model.Run.algorithmLaw
#modelClosure CountingMatroid.Model.Run.outputLaw
