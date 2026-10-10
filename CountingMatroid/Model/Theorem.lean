import CountingMatroid.Model.Run
import CountingMatroid.Model.Prior
import CountingMatroid.Analysis.TheoremProof

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
          x.2.bitOps ≤ C * (size + 1) ^ degree := by
    exact CountingMatroid.Analysis.TheoremProof.countingmatroid_main

end CountingMatroid
