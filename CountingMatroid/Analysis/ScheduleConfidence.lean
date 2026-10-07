import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: The charged schedule implements the paper's repetition count and
halving threshold, in the numerical form needed by amplification.
TEXLINE: main.tex:1442-1446 -/
theorem schedule_confidence_bound (n : ℕ) (p : CountingMatroid.Model.InputParams) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    s.repetitions = 10 * s.bδ + 1 ∧
      (1 / 2 : ENNReal) ^ s.bδ ≤ ENNReal.ofReal (p.δ : ℝ) := by
  constructor
  · dsimp [CountingMatroid.Interface.Pseudocode.setup, CountingMatroid.Program.schedule]
    simp [CountingMatroid.Model.Operations.successor,
      CountingMatroid.Model.Operations.natMul, Arlib.Computation.Charged.val_op]
  · -- The remaining inequality needs a value invariant for `Program.leastHalvings`.
    sorry

end CountingMatroid.Analysis.MedianAmplification
