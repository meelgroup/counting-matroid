import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false

namespace CountingMatroid.Analysis.SingleRunAccuracy

open CountingMatroid.Model

/-- PAPER: main.tex:1253-1421
The capped annealing run, fed one fresh finite fair-bit block, misses the
relative-error interval with probability at most one quarter. -/
theorem single_run_accuracy_bound (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let runLaw :=
      (CountingMatroid.Model.Run.fairTape
        (CountingMatroid.Model.Run.blockLength n r p)).map
        (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false) s)
    runLaw.toOuterMeasure
      {y : ℚ | y < (1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ) ∨
        (1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ) < y} ≤
      (1 / 4 : ENNReal) := by
  -- The paper's phase-mixing, estimation, and finite-bit coupling bounds
  -- need to be built before this calculation can close.
  unfold CountingMatroid.Interface.Pseudocode.singleRun
  dsimp only
  rw [PMF.toOuterMeasure_map_apply]
  sorry

end CountingMatroid.Analysis.SingleRunAccuracy
