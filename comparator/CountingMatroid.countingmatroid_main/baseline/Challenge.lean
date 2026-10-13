import CountingMatroid.Model.Run
import CountingMatroid.Model.Prior


set_option autoImplicit false

/-!
# Randomized common-base counting

The law in this statement is the `PMF` assembled in `Run` from independent
fair bits and the charged estimator. The existential solver is the paper's
single uniform deterministic feasibility pretest; constructing it remains an
obligation, not an additional oracle supplied by the caller.

The bound below uses `ExecutionCost.bitOps`, the model's charged count of
nonoracle operations. A concrete bit-operation RAM realization is still
missing, so that field does not yet certify the paper's physical bit bound.
The finite fair-bit block length also needs a coverage proof: out-of-range
reads currently default to false. These are gaps in the model, not extra
hypotheses in the theorem.
-/

namespace CountingMatroid

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- The paper's uniform randomized estimator, measured on the actual output
law. The bad event is the complement of the inclusive relative-error window;
the zero case and both work bounds hold on every possible execution. -/
theorem countingmatroid_main :
    ∃ (solver : FeasibilityImplementation) (C degree : ℕ),
      FeasibilityCorrect solver ∧
      ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (o₁ o₂ : IndependenceOracle n) (p : InputParams),
        FullGround M₁ M₂ → CommonRank r M₁ M₂ →
        ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
        let law := Model.Run.outputLaw solver n r o₁ o₂ p
        let Z : ℚ := commonBaseCount M₁ M₂
        let size := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹)
        law.toOuterMeasure
            {x | x.1 < (1 - p.ε) * Z ∨ (1 + p.ε) * Z < x.1} ≤
            ENNReal.ofReal (p.δ : ℝ) ∧
        (Z = 0 → ∀ x ∈ law.support, x.1 = 0) ∧
        ∀ x ∈ law.support,
          0 ≤ x.1 ∧
          x.2.oracleCalls ≤ C * (size + 1) ^ degree ∧
          x.2.bitOps ≤ C * (size + 1) ^ degree := by sorry

end CountingMatroid

/-!
HANDOFF NOTES
Review observations only; these notes do not change theorem status.
Statement match: paper — main.tex:86: “the number of other bit operations” is bounded on every execution.; Lean — ExecutionCost.bitOps is otherSteps run: fair-bit charges plus named RAM-instruction charges. Operations such as natMul attach one charge to arbitrary natural multiplication; encodeQuery and rational arithmetic attach prescribed tallies to already computed mathematical values. No representation relation or concrete machine execution appears in the headline.
Statement match: paper — The requested algorithm uses independent unbiased random bits. The supplied statement-shape discipline additionally requires the algorithm's distribution to arise directly from its control flow in PMF.; Lean — Run.algorithmLaw first samples fairBlocks, then returns Program.estimate applied to blockTape blocks. Individual program reads are deterministic accesses to externally sampled finite tapes, with false defaults outside their bounds. This is a seed-read-off denotation despite using PMF bind and pure.
Randomness semantics: Using PMF does not establish the required compositional denotation. algorithmLaw first samples complete finite tapes and then returns a deterministic execution: `let blocks ← fairBlocks repetitions (blockLength n r p); pure (CountingMatroid.Program.estimate ... (blockTape blocks))`. The program's adaptive draws occur through supplied tape lookups, rather than PMF binds at its sampling branches. This is a pushforward of external randomness, despite being expressed using PMF.
Audit surface (CountingMatroid.countingmatroid_main): The input and approximation claims agree, including quantifier order and error constants. The nonoracle counter is a charged mathematical surrogate without a machine realization, so bounding it does not establish the claimed bit-operation bound. The probability law samples finite seeds and reads them deterministically rather than composing sampling with program control flow. This is the only theorem declaration in the complete supplied Model files.. Lean claims: There exist a uniform charged feasibility solver and fixed C, degree. On all finite, full-ground, equal-rank matroid inputs with exact Boolean independence oracles and rational accuracy/confidence parameters in (0,1), its finite-fair-tape output law has relative-error failure mass at most δ. Every supported output is nonnegative, is zero when the common-base count is zero, and has charged oracle and nonoracle counts at most C(size+1)^degree.. Paper: main.tex:86 asserts the same approximation and zero-case guarantees for a single oracle algorithm, and bounds “the number of oracle calls and the number of other bit operations” on every execution.
-/
