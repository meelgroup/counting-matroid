import CountingMatroid.Model.Prelude
import CountingMatroid.Model.Operations

set_option autoImplicit false

/-!
# Subroutine interfaces and unresolved executable dependencies

Correspondence ledger:

* main.tex:283–293, 1529–1534: deterministic matroid-intersection feasibility
  pretest. `FeasibilityImplementation.run` is its **explicit missing charged code**;
  `FeasibilityContract` records its exact decision and separate polynomial call
  and bit-work obligations. Inputs are `n`, `r`, and exactly two fixed n-bit
  independence oracles. Validity requires `CommonRank` and both `ExactOracle`
  promises, and `FullGround`. Output is a Boolean saying whether
  `commonBaseCount > 0`. No installed
  Mathlib or Arlib executable matroid-intersection implementation or cost
  certificate was found. This is a borrowed algorithmic dependency cited by the
  paper, not an extra feasibility oracle and not a theorem proved here. A later
  pass must provide concrete code and a RAM realization before using the
  contract; no instance or `Classical.choose` is supplied.
* main.tex:1333–1346: `greedyRank`, `pairedProjections`, and `pairedRank`
  implement the original-oracle greedy scan and formula. Correctness against
  Mathlib rank and the RAM realization are same-paper **proof obligations**;
  no paired-rank oracle or abstract whole-step field is introduced.
* main.tex:746–751, 1163–1205, 1392–1421, 1442–1448: exchange transition,
  capped trace restart, phase observation/update, bounded rejection draws, and
  median amplification are the reduction's own composition. They have no
  subroutine implementation parameter here; Program writes their loops and
  abort branches explicitly.

`Arlib.Computation.StdImpl` is only a price table. This installed Arlib pin has
`RAM` but no `Realizes`, `StdRealizes`, `Buffer`, `WordLoop`, `Matrix`, or
`SignedWord` realization layer. Thus even a future charged feasibility solver
will still need a representation relation, RAM code, correctness, execution
cost, word/address bounds, initialization, allocation, and physical-capacity
proofs. Exact fair-bit output laws belong in Run, not this deterministic file.
-/

namespace CountingMatroid.Model.Subroutines

open CountingMatroid.Model
open CountingMatroid.Model.Operations

/-- Greedy rank of a represented subset, with at most one original-oracle query
per ground element. The body constructs each n-bit candidate query explicitly.
Its mathematical rank identity and RAM realization remain proof obligations. -/
def greedyRank {n : ℕ} (which : Bool) (oracle : IndependenceOracle n)
    (target : Finset (Fin n)) : Arlib.Computation.Charged Op Cell ℕ := do
  let result ← Arlib.Computation.Charged.foldl (fun acc i => do
    let present ← containsElement target i
    if present then
      let candidate ← insertElement acc.1 i
      let q ← encodeQuery candidate
      let independent ← oracleQuery which oracle q
      if independent then
        let size ← successor acc.2
        pure (candidate, size)
      else pure acc
    else pure acc) (List.finRange n) ((∅ : Finset (Fin n)), 0)
  pure result.2

/-- Scan a paired state into its x projection, the complement of its y
projection, and the number of present y elements. Every membership and insert
is routed through the charged operation vocabulary. -/
def pairedProjections {n : ℕ} (state : PairedSet n) :
    Arlib.Computation.Charged Op Cell
      (Finset (Fin n) × Finset (Fin n) × ℕ) :=
  Arlib.Computation.Charged.foldl (fun acc i => do
    let inX ← containsPaired state (i, false)
    let x ← if inX then insertElement acc.1 i else pure acc.1
    let inY ← containsPaired state (i, true)
    if inY then
      let ysize ← successor acc.2.2
      pure (x, acc.2.1, ysize)
    else
      let complementY ← insertElement acc.2.1 i
      pure (x, complementY, acc.2.2))
    (List.finRange n) ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)

/-- The paper's paired-rank formula, evaluated through the two original
independence oracles. Correctness against `M₁ ⊕ M₂*` is still to be proved. -/
def pairedRank {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (state : PairedSet n) : Arlib.Computation.Charged Op Cell ℕ := do
  let (x, complementY, ysize) ← pairedProjections state
  let rankX ← greedyRank false o₁ x
  let rankComplementY ← greedyRank true o₂ complementY
  let left ← natAdd rankX ysize
  let total ← natAdd left rankComplementY
  natSub total r

/-- An unresolved implementation parameter for the paper's cited deterministic
matroid-intersection pretest. It receives only the two original oracles. -/
structure FeasibilityImplementation where
  run : (n r : ℕ) → IndependenceOracle n → IndependenceOracle n →
    Arlib.Computation.Charged Op Cell Bool

/-- The number of original independence-oracle calls in the charged trace. -/
def oracleCalls {α : Type} (p : Arlib.Computation.Charged Op Cell α) : ℕ :=
  p.cost Op.oracleFirst + p.cost Op.oracleSecond

/-- The nonoracle primitive count: a fair-bit read or one named RAM instruction.
A bit-cost theorem additionally needs a concrete bounded-word realization. -/
def otherSteps {α : Type} (p : Arlib.Computation.Charged Op Cell α) : ℕ :=
  p.cost Op.fairBit +
    Arlib.Computation.Op.all.foldl (fun total instruction =>
      total + p.cost (Op.word instruction)) 0

/-- Exact correctness of the candidate pretest on every promised input. The
same-rank and oracle conditions remain caller guards; feasibility is not one. -/
noncomputable def FeasibilityCorrect (solver : FeasibilityImplementation) : Prop :=
  ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n),
    FullGround M₁ M₂ → CommonRank r M₁ M₂ →
      ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
      (solver.run n r o₁ o₂).val = decide (0 < commonBaseCount M₁ M₂)

/-- A fixed polynomial bound, uniform over all oracle answers and inputs. The
bit side counts the same charged pretest as the correctness statement. -/
def FeasibilityBounded (solver : FeasibilityImplementation)
    (callConstant callDegree bitConstant bitDegree : ℕ) : Prop :=
  ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n),
    oracleCalls (solver.run n r o₁ o₂) ≤
      callConstant * (n + r + 1) ^ callDegree ∧
    otherSteps (solver.run n r o₁ o₂) ≤
      bitConstant * (n + r + 1) ^ bitDegree

/-- A cited solver package, if one is later constructed. Its existence is
currently unresolved; this structure does not manufacture an implementation. -/
structure FeasibilityContract where
  implementation : FeasibilityImplementation
  callConstant : ℕ
  callDegree : ℕ
  bitConstant : ℕ
  bitDegree : ℕ
  correct : FeasibilityCorrect implementation
  bounded : FeasibilityBounded implementation
    callConstant callDegree bitConstant bitDegree

end CountingMatroid.Model.Subroutines
