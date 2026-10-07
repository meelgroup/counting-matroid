import CountingMatroid.Model.Run

set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputSupport

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: A possible charged run is the estimate on one supported finite
block sample. -/
theorem algorithmLaw_support_iff (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (run : Arlib.Computation.Charged Operations.Op Operations.Cell ℚ) :
    run ∈ (Model.Run.algorithmLaw solver n r o₁ o₂ p).support ↔
      ∃ blocks ∈ (Model.Run.fairBlocks
          (CountingMatroid.Program.schedule n p).val.repetitions
          (Model.Run.blockLength n r p)).support,
        CountingMatroid.Program.estimate solver n r o₁ o₂ p
          (Model.Run.blockTape blocks) = run := by
  change run ∈ (PMF.map
    (fun blocks => CountingMatroid.Program.estimate solver n r o₁ o₂ p
      (Model.Run.blockTape blocks))
    (Model.Run.fairBlocks
      (CountingMatroid.Program.schedule n p).val.repetitions
      (Model.Run.blockLength n r p))).support ↔ _
  exact PMF.mem_support_map_iff _ _ run

/-- INTERNAL: Expand the support of the charged output law to a possible
execution of the charged algorithm. -/
theorem outputLaw_support_iff (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (x : ℚ × ExecutionCost) :
    x ∈ (Model.Run.outputLaw solver n r o₁ o₂ p).support ↔
      ∃ run ∈ (Model.Run.algorithmLaw solver n r o₁ o₂ p).support,
        (run.val,
          { oracleCalls := oracleCalls run,
            bitOps := otherSteps run,
            randomBits := run.cost Operations.Op.fairBit }) = x := by
  change x ∈ (PMF.map
    (fun run : Arlib.Computation.Charged Operations.Op Operations.Cell ℚ =>
      (run.val,
        { oracleCalls := oracleCalls run,
          bitOps := otherSteps run,
          randomBits := run.cost Operations.Op.fairBit }))
    (Model.Run.algorithmLaw solver n r o₁ o₂ p)).support ↔ _
  exact PMF.mem_support_map_iff
      (fun run : Arlib.Computation.Charged Operations.Op Operations.Cell ℚ =>
        (run.val,
          { oracleCalls := oracleCalls run,
            bitOps := otherSteps run,
            randomBits := run.cost Operations.Op.fairBit }))
      (Model.Run.algorithmLaw solver n r o₁ o₂ p) x

end CountingMatroid.Analysis.OutputSupport
