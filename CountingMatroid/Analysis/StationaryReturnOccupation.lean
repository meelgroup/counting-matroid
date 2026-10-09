import CountingMatroid.Analysis.PositiveTimeTraceKernel

set_option autoImplicit false

/-!
Finite occupation bounds for positive-time returns. The first attempted step
is counted separately from the subsequent survival tails. Stationarity makes
the tails telescope, so neither irreducibility nor an infinite-expectation
interchange is needed. Operational finite-tape coupling is not asserted here.
-/
namespace CountingMatroid.Analysis.StationaryReturnOccupation

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: The stationary target mass plus the next H positive-time
survival tails, before dividing by target mass to condition the starting law.
The target mass counts the first attempted transition even on an immediate
return or a draw abort.
TEXLINE: main.tex:1072-1087 -/
noncomputable def returnOccupation (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (H : ℕ) : ℝ :=
  (∑ x ∈ A, μ x) + ∑ k ∈ Finset.range H,
    ∑ x, if x ∈ A then μ x * (∑ z, P x z * survive P A k z) else 0

/-- INTERNAL: The finite stationary excursion occupations telescope exactly;
the residual is stationary survival mass at the final horizon.
TEXLINE: main.tex:1072-1087 -/
theorem stationary_return_occupation (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (H : ℕ) :
    returnOccupation P A μ H = 1 - ∑ x, μ x * survive P A H x := by
  induction H with
  | zero =>
      simp only [returnOccupation, Finset.range_zero, Finset.sum_empty, add_zero]
      have hsplit : (∑ x ∈ A, μ x) + (∑ x, μ x * survive P A 0 x) = 1 := by
        rw [← μ.sum_coe]
        have hA : (∑ x ∈ A, μ x) = (∑ x, if x ∈ A then μ x else 0) := by simp
        rw [hA]
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ A <;> simp [survive, offTarget, hx]
      linarith
  | succ H ih =>
      rw [returnOccupation, Finset.sum_range_succ]
      rw [← add_assoc]
      change returnOccupation P A μ H +
        (∑ x, if x ∈ A then μ x * (∑ z, P x z * survive P A H z) else 0) = _
      rw [ih, stationary_survival_drop P A μ hstationary H]
      ring

/-- INTERNAL: A U-warm positive-time return has finite occupation budget
at most U times any inverse-target-mass bound B. Missing operational mass
can be dominated by this budget without conditioning successful returns.
TEXLINE: main.tex:1072-1087,1226-1234 -/
theorem warm_return_occupation_le (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hstationary : Stationary μ P) (H : ℕ)
    (U B : ℝ) (hU : 0 ≤ U) (hmass : 0 < ∑ x ∈ A, μ x)
    (hB : 1 ≤ B * (∑ x ∈ A, μ x)) :
    U / (∑ x ∈ A, μ x) * returnOccupation P A μ H ≤ U * B := by
  have hocc : returnOccupation P A μ H ≤ 1 := by
    rw [stationary_return_occupation P A μ hstationary H]
    have hnonneg : 0 ≤ ∑ x, μ x * survive P A H x :=
      Finset.sum_nonneg fun x _ => mul_nonneg (μ.coe_nonneg x) (survive_nonneg P A H x)
    linarith
  calc
    U / (∑ x ∈ A, μ x) * returnOccupation P A μ H ≤
        U / (∑ x ∈ A, μ x) * 1 :=
      mul_le_mul_of_nonneg_left hocc (div_nonneg hU hmass.le)
    _ ≤ U * B := by
      rw [mul_one, div_le_iff₀ hmass]
      nlinarith [mul_le_mul_of_nonneg_left hB hU]

end CountingMatroid.Analysis.StationaryReturnOccupation
