import CountingMatroid.Analysis.TransversalTraceSpectralGap
import Arlib.MarkovChains.Techniques.SpectralGap
import Arlib.MarkovChains.Techniques.Comparison

set_option autoImplicit false

/-!
Pointwise finite-chain mixing from the library's variance contraction. A
uniform lower bound on the stationary law converts squared-error decay into
the factor-two endpoint density needed for the warm restart argument.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceMixing

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: A spectral contraction smaller than the minimum stationary
mass gives pointwise factor-two domination of every row after k steps.
TEXLINE: main.tex:1070-1079,1219-1223 -/
theorem pointwise_mixing_le_of_gap {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (μ : FinDist Ω) (P : FinChain Ω) (hrev : Reversible μ P)
    (hpsd : NonnegDefinite μ P) (γ m : ℝ)
    (hgap : SpectralGapAtLeast μ P γ) (hγ : γ ≤ 1)
    (hm : 0 < m) (hmin : ∀ x, m ≤ μ x) (k : ℕ)
    (hdecay : (1 - γ) ^ k ≤ m) (x y : Ω) : P.iter k x y ≤ 2 * μ y := by
  let f : Ω → ℝ := fun z => if z = y then 1 else 0
  have hfmean : Ex μ f = μ y := by simp [Ex, f]
  have hfvar : Var μ f ≤ μ y := by
    rw [Var_eq_ip_sub_sq, hfmean]
    have hself : ip μ f f = μ y := by simp [ip, f]
    rw [hself]
    nlinarith [sq_nonneg (μ y)]
  have hact : (P.iter k).act f x = P.iter k x y := by simp [FinKernel.act, f]
  have hmean : Ex μ ((P.iter k).act f) = μ y := by
    rw [Ex_act_of_stationary (iter_stationary hrev.stationary k), hfmean]
  have hpoint : μ x * (P.iter k x y - μ y) ^ 2 ≤ Var μ ((P.iter k).act f) := by
    rw [Var_apply]
    have hs := Finset.single_le_sum (s := Finset.univ) (a := x)
      (f := fun z => μ z * ((P.iter k).act f z - Ex μ ((P.iter k).act f)) ^ 2)
      (fun z _ => mul_nonneg (μ.coe_nonneg z) (sq_nonneg _)) (Finset.mem_univ x)
    simpa only [hmean, hact] using hs
  have hvar := Var_iter_le_of_gap hrev hpsd hgap hγ f k
  have hpow : ((1 - γ) ^ 2) ^ k = ((1 - γ) ^ k) ^ 2 := by
    simp only [← pow_mul, Nat.mul_comm]
  rw [hpow] at hvar
  have hpow0 : 0 ≤ (1 - γ) ^ k := pow_nonneg (by linarith) k
  have hdecay2 : ((1 - γ) ^ k) ^ 2 ≤ m ^ 2 := by
    nlinarith
  have hminprod : m ^ 2 ≤ μ x * μ y := by
    have hprod := mul_le_mul (hmin x) (hmin y) hm.le (μ.coe_nonneg x)
    nlinarith
  have hpoint2 : μ x * (P.iter k x y - μ y) ^ 2 ≤ μ x * (μ y) ^ 2 := by
    calc
      _ ≤ ((1 - γ) ^ k) ^ 2 * Var μ f := hpoint.trans hvar
      _ ≤ ((1 - γ) ^ k) ^ 2 * μ y :=
        mul_le_mul_of_nonneg_left hfvar (sq_nonneg _)
      _ ≤ m ^ 2 * μ y := mul_le_mul_of_nonneg_right hdecay2 (μ.coe_nonneg y)
      _ ≤ (μ x * μ y) * μ y := mul_le_mul_of_nonneg_right hminprod (μ.coe_nonneg y)
      _ = _ := by ring
  have hx : 0 < μ x := hm.trans_le (hmin x)
  have he := le_of_mul_le_mul_left hpoint2 hx
  have habs : |P.iter k x y - μ y| ≤ μ y := by
    apply (sq_le_sq₀ (abs_nonneg _) (μ.coe_nonneg y)).mp
    simpa only [sq_abs] using he
  linarith [(abs_le.mp habs).2]

end CountingMatroid.Analysis.PositiveTimeTraceMixing
