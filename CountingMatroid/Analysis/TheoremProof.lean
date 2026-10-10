import CountingMatroid.Model.Run
import CountingMatroid.Model.Prior
import CountingMatroid.Interface.Encoding
import CountingMatroid.Interface.Pseudocode
import CountingMatroid.Interface.ProgramModel
import CountingMatroid.Analysis.FeasibilitySolver
import CountingMatroid.Analysis.OutputAccuracy
import CountingMatroid.Analysis.ResourceBound

set_option autoImplicit false

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- PAPER: main.tex:86-104, 1442-1470
Proof-side assembly for `CountingMatroid.countingmatroid_main`. Its three proof
dependencies are the cited pretest, the annealing accuracy argument, and the
charged cost bound. -/
theorem CountingMatroid.Analysis.TheoremProof.countingmatroid_main :
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
  obtain ⟨contract⟩ :=
    CountingMatroid.Analysis.FeasibilitySolver.exists_feasibility_contract
  obtain ⟨C, degree, hresource⟩ :=
    CountingMatroid.Analysis.ResourceBound.output_resource_bound contract
  refine ⟨contract.implementation, C, degree, contract.correct, ?_⟩
  intro n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂
  have haccuracy :=
    CountingMatroid.Analysis.OutputAccuracy.output_accuracy
      contract.implementation contract.correct n r M₁ M₂ o₁ o₂ p
      hfull hr h₁ h₂
  have hrle : r ≤ n := by
    have hle : M₁.eRank ≤ (n : ENat) := by
      calc
        M₁.eRank ≤ M₁.E.encard := M₁.eRank_le_encard_ground
        _ = (n : ENat) := by simp [hfull.1]
    rw [hr.1] at hle
    exact_mod_cast hle
  exact ⟨haccuracy.1, haccuracy.2, hresource n r o₁ o₂ p hrle⟩

