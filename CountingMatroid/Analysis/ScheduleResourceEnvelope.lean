import CountingMatroid.Model.Run

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleResourceEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The concrete schedule base is nonnegative, including the empty ground.
TEXLINE: main.tex:1109-1116 -/
theorem schedule_rho_nonneg (n : ℕ) (p : InputParams) :
   0 ≤ (CountingMatroid.Program.schedule n p).val.ρ := by
  dsimp [CountingMatroid.Program.schedule]
  simp only [ratDiv, ratSub, natMul, ratOfNat, Arlib.Computation.Charged.val_op,
    Arlib.Computation.Charged.val_opMany]
  by_cases hn : n = 0
  · simp [hn]
  · have hnpos : (0 : ℚ) < (n : ℚ) := by exact_mod_cast Nat.pos_of_ne_zero hn
    have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hn)
    have hle : (1 : ℚ) ≤ 2 * n := by linarith
    have hdiv : (1 : ℚ) / (2 * n) ≤ 1 := by
      apply (div_le_iff₀ (by positivity)).2
      simpa using hle
    have hdivNat : (1 : ℚ) / (↑(2 * n) : ℚ) ≤ 1 := by
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hdiv
    linarith

/-- INTERNAL: The charged schedule construction produces polynomially bounded
loop caps and a nonnegative annealing base. This is independent of the phase
state and of the median computation.
TEXLINE: main.tex:1348-1356, 1397-1421 -/
theorem schedule_resource_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let schedule := CountingMatroid.Program.schedule n p
      let s := schedule.val
      0 ≤ s.ρ ∧
      n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
        binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree ∧
      oracleCalls schedule ≤ C * inputSize ^ degree ∧
      otherSteps schedule ≤ C * inputSize ^ degree := by
  -- The sign condition is discharged directly from the concrete charged schedule.
  -- The remaining obligation is only the common polynomial envelope for values
  -- and charged arithmetic. In particular it does not need a separate claim
  -- that either bounded search reaches its mathematical threshold.
  have hpoly :
      ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
        let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
          binaryNatLength (Nat.ceil p.δ⁻¹) + 1
        let schedule := CountingMatroid.Program.schedule n p
        let s := schedule.val
        n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
          binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree ∧
        oracleCalls schedule ≤ C * inputSize ^ degree ∧
        otherSteps schedule ≤ C * inputSize ^ degree := by
    -- BLOCKER: prove binary-length bounds for intermediate rational values
    -- (especially ε / (32(L+1)) and the observation quotient), then sum the
    -- charged primitive costs through the two bounded folds. The generic
    -- `steps_repeatWhile_le` controls total iterations but not operand sizes.
    sorry
  obtain ⟨C, degree, hpoly⟩ := hpoly
  refine ⟨C, degree, ?_⟩
  intro n r p
  exact ⟨schedule_rho_nonneg n p, hpoly n r p⟩

end CountingMatroid.Analysis.ScheduleResourceEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r7 · repaired · isolated the nonnegative schedule base; the remaining envelope requires intermediate rational encoding bounds.
* r6 · open · isolated schedule arithmetic from the capped-run state invariant.
-/
