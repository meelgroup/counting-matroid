import CountingMatroid.Analysis.PositiveTimeTraceKernel
import Arlib.MarkovChains.Techniques.Dirichlet

set_option autoImplicit false

/-!
Harmonic extension for the concrete positive-time return subkernel. The
extension uses the increasing finite hitting kernels, so the first-step
identities do not assume almost-sure hitting from zero-weight states.
-/
namespace CountingMatroid.Analysis.PositiveTimeTraceHarmonic

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Finite zero-time hitting entries increase with their horizon.
TEXLINE: main.tex:1047-1053 -/
theorem hitWithin_monotone (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    Monotone (fun k => (hitWithin P A k).entry x y) :=
  monotone_nat_of_le_succ (fun k => hitWithin_succ_le P A k x y)

/-- INTERNAL: Hitting entries obey the same unit budget as the finite rows. -/
theorem hitWithin_bddAbove (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    BddAbove (Set.range (fun k => (hitWithin P A k).entry x y)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨k, rfl⟩
  exact entry_le_one _ x y

/-- INTERNAL: The uncapped zero-time hitting array, including immediate hits.
TEXLINE: main.tex:1047-1053 -/
noncomputable def uncappedHit (P : FinChain Ω) (A : Finset Ω) (x y : Ω) : ℝ :=
  ⨆ k, (hitWithin P A k).entry x y

/-- INTERNAL: Finite zero-time hitting converges to its uncapped entries. -/
theorem hitWithin_tendsto (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    Filter.Tendsto (fun k => (hitWithin P A k).entry x y) Filter.atTop
      (nhds (uncappedHit P A x y)) :=
  tendsto_atTop_ciSup (hitWithin_monotone P A x y) (hitWithin_bddAbove P A x y)

/-- INTERNAL: The uncapped zero-time hit fixes every target state.
TEXLINE: main.tex:1047-1053 -/
theorem uncappedHit_on_target (P : FinChain Ω) (A : Finset Ω) (x y : Ω)
    (hx : x ∈ A) : uncappedHit P A x y = if x = y then 1 else 0 := by
  simp only [uncappedHit, hitWithin_on_target P A _ x y hx, ciSup_const]

/-- INTERNAL: The uncapped hitting endpoint stays in the target set. -/
theorem uncappedHit_supported (P : FinChain Ω) (A : Finset Ω) (x y : Ω)
    (hy : y ∉ A) : uncappedHit P A x y = 0 := by
  simp only [uncappedHit, hitWithin_supported P A _ x y hy, ciSup_const]

/-- INTERNAL: Passing the finite return recursion to its monotone limit
identifies a positive return as one step followed by a zero-time hit.
TEXLINE: main.tex:1047-1055 -/
theorem uncappedReturn_first_step (P : FinChain Ω) (A : Finset Ω) (x y : Ω) :
    (uncappedReturn P A).entry x y = ∑ z, P x z * uncappedHit P A z y := by
  have hfinite (k : ℕ) : (returnWithin P A (k + 1)).entry x y =
      ∑ z, P x z * (hitWithin P A k).entry z y := rfl
  have hleft := (returnWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1)
  have hright := tendsto_finsetSum Finset.univ
    (fun z _ => (hitWithin_tendsto P A z y).const_mul (P x z))
  exact tendsto_nhds_unique hleft (by simpa only [Function.comp_def, hfinite] using hright)

/-- INTERNAL: The off-target first-step equation for uncapped zero-time hits.
TEXLINE: main.tex:1047-1055 -/
theorem uncappedHit_off_target (P : FinChain Ω) (A : Finset Ω) (x y : Ω)
    (hx : x ∉ A) : uncappedHit P A x y = (uncappedReturn P A).entry x y := by
  have hfinite (k : ℕ) : (hitWithin P A (k + 1)).entry x y =
      (returnWithin P A (k + 1)).entry x y := by
    simp only [hitWithin, hx, if_false, returnWithin]
  exact tendsto_nhds_unique
    ((hitWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1))
    (by simpa only [Function.comp_def, hfinite, uncappedReturn] using
      (returnWithin_tendsto P A x y).comp (Filter.tendsto_add_atTop_nat 1))

/-- INTERNAL: Canonical harmonic extension obtained from uncapped hitting.
TEXLINE: main.tex:1047-1053 -/
noncomputable def harmonicExtension (P : FinChain Ω) (A : Finset Ω)
    (h : Ω → ℝ) (x : Ω) : ℝ := ∑ y, uncappedHit P A x y * h y

/-- INTERNAL: The extension retains its prescribed boundary values.
TEXLINE: main.tex:1047-1053 -/
theorem harmonicExtension_on_target (P : FinChain Ω) (A : Finset Ω)
    (h : Ω → ℝ) (x : Ω) (hx : x ∈ A) : harmonicExtension P A h x = h x := by
  simp [harmonicExtension, uncappedHit_on_target P A x _ hx]

/-- PAPER: main.tex:1051-1055
The residual of the harmonic extension vanishes off the target and equals
the positive-time trace residual on the target. -/
theorem harmonic_extension_residual (P : FinChain Ω) (A : Finset Ω)
    (h : Ω → ℝ) (x : Ω) :
    harmonicExtension P A h x - P.act (harmonicExtension P A h) x =
      if x ∈ A then h x - ∑ y, (uncappedReturn P A).entry x y * h y else 0 := by
  have hact : P.act (harmonicExtension P A h) x =
      ∑ y, (uncappedReturn P A).entry x y * h y := by
    simp only [FinKernel.act, harmonicExtension, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp_rw [uncappedReturn_first_step, Finset.sum_mul, mul_assoc]
  rw [hact]
  by_cases hx : x ∈ A
  · rw [if_pos hx, harmonicExtension_on_target P A h x hx]
  · rw [if_neg hx]
    simp only [harmonicExtension, uncappedHit_off_target P A x _ hx, sub_self]

/-- PAPER: main.tex:1056-1063
Harmonic extension transfers the underlying Dirichlet form to the trace
boundary without requiring full support off the boundary. -/
theorem harmonic_extension_energy (μ : FinDist Ω) (P : FinChain Ω)
    (A : Finset Ω) (f g : Ω → ℝ) :
    dirichlet μ P (harmonicExtension P A f) (harmonicExtension P A g) =
      ∑ x ∈ A, μ x * f x *
        (g x - ∑ y, (uncappedReturn P A).entry x y * g y) := by
  unfold dirichlet ip
  rw [← Finset.sum_sub_distrib]
  calc
    _ = ∑ x, μ x * harmonicExtension P A f x *
        (harmonicExtension P A g x - P.act (harmonicExtension P A g) x) := by
      apply Finset.sum_congr rfl
      intro x _
      ring
    _ = ∑ x, if x ∈ A then μ x * f x *
        (g x - ∑ y, (uncappedReturn P A).entry x y * g y) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      rw [harmonic_extension_residual]
      by_cases hx : x ∈ A
      · rw [if_pos hx, if_pos hx, harmonicExtension_on_target P A f x hx]
      · rw [if_neg hx, if_neg hx, mul_zero]
    _ = _ := by rw [← Finset.sum_filter]; simp

/-- PAPER: main.tex:1056-1058
Symmetry of the underlying Dirichlet form gives detailed balance of the
positive-time trace at boundary states, including zero stationary weights. -/
theorem uncappedReturn_reversible (μ : FinDist Ω) (P : FinChain Ω)
    (hrev : Reversible μ P) (A : Finset Ω) (x y : Ω)
    (hx : x ∈ A) (hy : y ∈ A) :
    μ x * (uncappedReturn P A).entry x y =
      μ y * (uncappedReturn P A).entry y x := by
  classical
  by_cases hxy : x = y
  · subst y; rfl
  let f : Ω → ℝ := fun z => if z = x then 1 else 0
  let g : Ω → ℝ := fun z => if z = y then 1 else 0
  have hfg := dirichlet_comm hrev (harmonicExtension P A f) (harmonicExtension P A g)
  rw [harmonic_extension_energy, harmonic_extension_energy] at hfg
  have hleft : (∑ z ∈ A, μ z * f z *
      (g z - ∑ w, (uncappedReturn P A).entry z w * g w)) =
      - (μ x * (uncappedReturn P A).entry x y) := by
    simp [f, g, hx, hxy]
  have hright : (∑ z ∈ A, μ z * g z *
      (f z - ∑ w, (uncappedReturn P A).entry z w * f w)) =
      - (μ y * (uncappedReturn P A).entry y x) := by
    simp [f, g, hy, (Ne.symm hxy)]
  rw [hleft, hright] at hfg
  exact neg_injective hfg

/-- PAPER: main.tex:1058-1059
A positive-time return includes each one-step transition inside the target,
so in particular the trace inherits every underlying holding probability. -/
theorem uncappedReturn_ge_transition (P : FinChain Ω) (A : Finset Ω)
    (x y : Ω) (hy : y ∈ A) :
    P x y ≤ (uncappedReturn P A).entry x y := by
  apply le_trans ?_ (returnWithin_le_uncapped P A 1 x y)
  change P x y ≤ ∑ z, P x z * (targetIdentity A).entry z y
  have heq : (∑ z, P x z * (targetIdentity A).entry z y) = P x y := by
    have hcell (z : Ω) : P x z * (targetIdentity A).entry z y =
        if z = y then P x y else 0 := by
      by_cases hzy : z = y
      · subst z; simp [targetIdentity, hy]
      · simp [targetIdentity, hzy]
    simp [hcell]
  exact heq.ge

end CountingMatroid.Analysis.PositiveTimeTraceHarmonic

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · monotone hitting limits give the harmonic residual and boundary energy identity; symmetry proves trace detailed balance, and one-step returns preserve holding probabilities. No almost-sure-hitting assumption on zero-weight states is needed.
-/
