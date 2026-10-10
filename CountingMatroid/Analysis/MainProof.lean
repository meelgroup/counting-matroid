import CountingMatroid.Analysis.TheoremProof

set_option autoImplicit false

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- Compatibility alias for the proof-side assembly. -/
theorem CountingMatroid.Analysis.MainProof.countingmatroid_main :
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

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · decomposed · connected the cited pretest, accuracy, and resource obligations; the three child proofs remain open.
-/
