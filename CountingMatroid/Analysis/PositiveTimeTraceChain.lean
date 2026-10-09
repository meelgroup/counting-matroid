import CountingMatroid.Analysis.PositiveTimeTraceHarmonic

set_option autoImplicit false

/-!
The concrete uncapped positive-time trace as a finite stochastic chain on its
boundary. Its law is the conditional underlying stationary law, and finite
powers agree with the previously constructed return subkernel iterates.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceChain

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.PositiveTimeTraceHarmonic

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Rewrite a full finite sum supported on a boundary as its
subtype sum. This retains zero mass outside the trace state space. -/
theorem sum_on_target (A : Finset Ω) (f : Ω → ℝ)
    (hf : ∀ x, x ∉ A → f x = 0) :
    (∑ x, f x) = ∑ x : A, f x := by
  rw [← Finset.sum_subtype A (fun _ => Iff.rfl)]
  symm
  apply Finset.sum_subset (Finset.subset_univ A)
  intro x _ hx
  exact hf x hx

/-- INTERNAL: Restrict the underlying stationary law to a positive-mass
boundary and normalize it, giving the paper's transversal law.
TEXLINE: main.tex:1023-1037 -/
noncomputable def traceLaw (μ : FinDist Ω) (A : Finset Ω)
    (hA : 0 < ∑ x ∈ A, μ x) : FinDist A where
  p x := μ x / (∑ z ∈ A, μ z)
  p_nonneg x := div_nonneg (μ.coe_nonneg x) hA.le
  p_sum := by
    rw [← Finset.sum_div, ← Finset.sum_subtype A (fun _ => Iff.rfl)]
    exact div_self hA.ne'

/-- INTERNAL: Almost-sure return at positive stationary boundary states
makes the concrete return kernel stochastic on the boundary subtype.
TEXLINE: main.tex:1023-1037 -/
noncomputable def traceChain (μ : FinDist Ω) (P : FinChain Ω)
    (hstationary : Stationary μ P) (A : Finset Ω)
    (hμ : ∀ x ∈ A, 0 < μ x) : FinChain A where
  P x y := (uncappedReturn P A).entry x y
  P_nonneg x y := (uncappedReturn P A).nonneg x y
  P_sum x := by
    rw [← sum_on_target A (fun y => (uncappedReturn P A).entry x y)
      (fun y hy => uncappedReturn_supported P A x y hy)]
    exact uncappedReturn_mass_eq_one P A μ hstationary x x.property (hμ x x.property)

/-- PAPER: main.tex:1033-1037,1056-1058
The concrete trace is reversible with its conditional stationary law. -/
theorem trace_chain_reversible (μ : FinDist Ω) (P : FinChain Ω)
    (hrev : Reversible μ P) (A : Finset Ω)
    (hμ : ∀ x ∈ A, 0 < μ x) (hA : 0 < ∑ x ∈ A, μ x) :
    Reversible (traceLaw μ A hA) (traceChain μ P hrev.stationary A hμ) := by
  intro x y
  change (μ x / _) * (uncappedReturn P A).entry x y =
    (μ y / _) * (uncappedReturn P A).entry y x
  rw [div_mul_eq_mul_div, div_mul_eq_mul_div,
    uncappedReturn_reversible μ P hrev A x y x.property y.property]

/-- PAPER: main.tex:1033-1037,1058-1059
The concrete trace inherits half-laziness from the underlying chain. -/
theorem trace_chain_holding (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω)
    (hμ : ∀ x ∈ A, 0 < μ x) (hhold : ∀ x, (1 / 2 : ℝ) ≤ P x x)
    (x : A) : (1 / 2 : ℝ) ≤ traceChain μ P hst A hμ x x :=
  (hhold x).trans (uncappedReturn_ge_transition P A x x x.property)

/-- INTERNAL: Restricting to the boundary commutes with every finite power
of the concrete positive-time return subkernel.
TEXLINE: main.tex:1038-1043,1219-1223 -/
theorem trace_chain_iter (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω) (hμ : ∀ x ∈ A, 0 < μ x)
    (k : ℕ) (x y : A) :
    (traceChain μ P hst A hμ).iter k x y =
      (iterate (uncappedReturn P A) k).entry x y := by
  induction k generalizing x y with
  | zero =>
      change (if x = y then (1 : ℝ) else 0) = if (x : Ω) = y then 1 else 0
      simp only [Subtype.ext_iff]
  | succ k ih =>
      change (∑ z : A, (uncappedReturn P A).entry x z *
        (traceChain μ P hst A hμ).iter k z y) =
        ∑ z, (uncappedReturn P A).entry x z * (iterate (uncappedReturn P A) k).entry z y
      simp_rw [ih]
      symm
      apply sum_on_target A
      intro z hz
      rw [uncappedReturn_supported P A x z hz, zero_mul]

/-- PAPER: main.tex:1060-1063
Harmonic extension identifies trace Dirichlet energy with underlying energy
scaled by the probability mass of the boundary. -/
theorem trace_chain_energy (μ : FinDist Ω) (P : FinChain Ω)
    (hst : Stationary μ P) (A : Finset Ω) (hμ : ∀ x ∈ A, 0 < μ x)
    (hA : 0 < ∑ x ∈ A, μ x) (h : Ω → ℝ) :
    dirichlet μ P (harmonicExtension P A h) (harmonicExtension P A h) =
      (∑ x ∈ A, μ x) * dirichlet (traceLaw μ A hA)
        (traceChain μ P hst A hμ) (fun x => h x) (fun x => h x) := by
  rw [harmonic_extension_energy]
  have hact (x : A) : (traceChain μ P hst A hμ).act (fun y => h y) x =
      ∑ y, (uncappedReturn P A).entry x y * h y := by
    symm
    apply sum_on_target A
    intro y hy
    rw [uncappedReturn_supported P A x y hy, zero_mul]
  unfold dirichlet ip
  rw [← Finset.sum_sub_distrib, Finset.mul_sum,
    Finset.sum_subtype A (fun _ => Iff.rfl)]
  apply Finset.sum_congr rfl
  intro x _
  rw [hact]
  change μ x * h x * (h x - _) = (∑ z ∈ A, μ z) *
    ((μ x / (∑ z ∈ A, μ z)) * h x * h x -
      (μ x / (∑ z ∈ A, μ z)) * h x * _)
  field_simp

end CountingMatroid.Analysis.PositiveTimeTraceChain

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · constructed the stochastic trace on the boundary subtype, its reversible conditional law, holding probability, exact finite-power bridge, and harmonic-extension energy scaling.
-/
