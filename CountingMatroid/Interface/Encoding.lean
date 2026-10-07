import Mathlib.Probability.ProbabilityMassFunction.Constructions
import CountingMatroid.Model.Run

set_option autoImplicit false

/-!
# Answer-side interface for the charged estimator

Correspondence to the algorithm transcript: `Program.estimate` performs the
pretest (main.tex:283–293), the capped annealing runs (main.tex:1105–1205,
1392–1421), and median amplification (main.tex:1442–1448). `programAnswer`
reads only its rational answer. `answerLaw` forgets the charge in
`Run.algorithmLaw`, leaving the pseudocode-side distribution for correctness
proofs. Neither view is an executable step of the estimator.

The present Model uses its own `Operations.Op` and `Operations.Cell` directly;
it has no operation-class indirection to collapse into Arlib's `StdOp` or
`Cell`. Its paired states are `Finset`s rather than sealed carriers. Thus this
file has no carrier-read views beyond Arlib's existing `Charged.val`.
-/

namespace CountingMatroid.Interface

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- The rational answer of one charged execution on fixed fair-bit tapes. -/
noncomputable def programAnswer (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) : ℚ :=
  (CountingMatroid.Program.estimate solver n r o₁ o₂ p tape).val

@[simp] theorem programAnswer_eq (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) :
    programAnswer solver n r o₁ o₂ p tape =
      (CountingMatroid.Program.estimate solver n r o₁ o₂ p tape).val := rfl

/-- The law of the answer alone, projected from the program's charged law. -/
noncomputable def answerLaw (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) : PMF ℚ :=
  (CountingMatroid.Model.Run.algorithmLaw solver n r o₁ o₂ p).map
    Arlib.Computation.Charged.val

@[simp] theorem answerLaw_eq (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) :
    answerLaw solver n r o₁ o₂ p =
      (CountingMatroid.Model.Run.algorithmLaw solver n r o₁ o₂ p).map
        Arlib.Computation.Charged.val := rfl

end CountingMatroid.Interface
