import Arlib.MarkovChains.Techniques.Dirichlet
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.BigOperators.Field

set_option autoImplicit false

/-!
Finite product-path expectations and moments. The last transition is unused
by the observations, matching the stationary observation experiment.
-/
namespace CountingMatroid.Analysis.StationaryPathMoment

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω]

/-- INTERNAL: Product weight of a path with N transitions. -/
noncomputable def pathWeight (P : FinChain Ω) (N : ℕ)
    (path : Fin (N + 1) → Ω) : ℝ :=
  ∏ i : Fin N, P (path i.castSucc) (path i.succ)

/-- INTERNAL: The N observations at the first N vertices of a path. -/
noncomputable def observationSum (g : Ω → ℝ) (N : ℕ)
    (path : Fin (N + 1) → Ω) : ℝ :=
  ∑ i : Fin N, g (path i.castSucc)

/-- INTERNAL: Split a finite path sum at its first vertex. -/
theorem sum_paths_cons (N : ℕ) (F : (Fin (N + 2) → Ω) → ℝ) :
    (∑ path, F path) = ∑ x : Ω, ∑ path : Fin (N + 1) → Ω, F (Fin.cons x path) := by
  classical
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (N + 2) => Ω)) F]
  exact Fintype.sum_prod_type _

/-- INTERNAL: Splitting off the first transition factors the product weight. -/
theorem path_weight_cons (P : FinChain Ω) (N : ℕ) (x : Ω)
    (path : Fin (N + 1) → Ω) :
    pathWeight P (N + 1) (Fin.cons x path) = P x (path 0) * pathWeight P N path := by
  classical
  unfold pathWeight
  rw [Fin.prod_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
    ← Fin.succ_castSucc]

/-- INTERNAL: Splitting off the first observation leaves the suffix sum. -/
theorem observation_sum_cons (g : Ω → ℝ) (N : ℕ) (x : Ω)
    (path : Fin (N + 1) → Ω) :
    observationSum g (N + 1) (Fin.cons x path) = g x + observationSum g N path := by
  classical
  unfold observationSum
  rw [Fin.sum_univ_succ]
  simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ,
    ← Fin.succ_castSucc]

/-- INTERNAL: Summing the product-path law against its initial weight
preserves the total mass, for arbitrary real initial weights. -/
theorem path_mass (P : FinChain Ω) (N : ℕ) (w : Ω → ℝ) :
    (∑ path : Fin (N + 1) → Ω, w (path 0) * pathWeight P N path) = ∑ x, w x := by
  classical
  induction N generalizing w with
  | zero =>
    simp only [pathWeight, Fin.prod_univ_zero, mul_one]
    exact Equiv.sum_comp (Equiv.funUnique (Fin 1) Ω) w
  | succ N ih =>
    rw [sum_paths_cons N]
    simp only [Fin.cons_zero, path_weight_cons, ← mul_assoc]
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    rw [ih (fun y => ∑ x, w x * P x y)]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, P.sum_coe, mul_one]

/-- INTERNAL: The first moment of a finite observation sum is the sum
of the iterated actions, even for signed initial weights.
TEXLINE: main.tex:1002-1013 -/
theorem path_first_moment [DecidableEq Ω] (P : FinChain Ω)
    (g w : Ω → ℝ) (N : ℕ) :
    (∑ path : Fin (N + 1) → Ω,
      w (path 0) * pathWeight P N path * observationSum g N path) =
      ∑ t ∈ Finset.range N, ∑ x, w x * (P.iter t).act g x := by
  classical
  induction N generalizing w with
  | zero => simp [observationSum]
  | succ N ih =>
    rw [sum_paths_cons N]
    simp only [Fin.cons_zero, path_weight_cons, observation_sum_cons]
    have hexpand (x : Ω) (path : Fin (N + 1) → Ω) :
        w x * (P x (path 0) * pathWeight P N path) *
          (g x + observationSum g N path) =
        (w x * P x (path 0)) * pathWeight P N path * g x +
          (w x * P x (path 0)) * pathWeight P N path * observationSum g N path := by ring
    simp_rw [hexpand]
    simp_rw [Finset.sum_add_distrib]
    have hfirst : (∑ x : Ω, ∑ path : Fin (N + 1) → Ω,
        (w x * P x (path 0)) * pathWeight P N path * g x) =
        ∑ x, w x * g x := by
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_mul, path_mass P N (fun y => w x * P x y)]
      rw [← Finset.mul_sum, P.sum_coe, mul_one]
    rw [hfirst]
    have htail : (∑ x : Ω, ∑ path : Fin (N + 1) → Ω,
        (w x * P x (path 0)) * pathWeight P N path * observationSum g N path) =
        ∑ t ∈ Finset.range N, ∑ x, w x * (P.iter (t + 1)).act g x := by
      rw [Finset.sum_comm]
      simp only [← Finset.sum_mul]
      rw [ih (fun y => ∑ x, w x * P x y)]
      apply Finset.sum_congr rfl
      intro t _
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x _
      rw [FinKernel.act_iter_succ]
      simp only [FinKernel.act, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _
      ring
    rw [htail, Finset.sum_range_succ']
    simp only [FinKernel.iter_zero, FinKernel.act_id]
    ring

/-- INTERNAL: Unnormalised second moment of the sum of N observations. -/
noncomputable def pathSquaredSum (π : FinDist Ω) (P : FinChain Ω)
    (g : Ω → ℝ) (N : ℕ) : ℝ :=
  ∑ path : Fin (N + 1) → Ω,
    π (path 0) * pathWeight P N path * (observationSum g N path) ^ 2

/-- INTERNAL: Adding the first stationary observation contributes its
variance and twice its covariances with the suffix.
TEXLINE: main.tex:1010-1013 -/
theorem stationary_square_succ [DecidableEq Ω] (π : FinDist Ω)
    (P : FinChain Ω) (hst : Stationary π P) (g : Ω → ℝ) (N : ℕ) :
    pathSquaredSum π P g (N + 1) = pathSquaredSum π P g N + ip π g g +
      2 * ∑ t ∈ Finset.range N, ip π g ((P.iter (t + 1)).act g) := by
  classical
  unfold pathSquaredSum
  rw [sum_paths_cons N]
  simp only [Fin.cons_zero, path_weight_cons, observation_sum_cons]
  have hexpand (x : Ω) (path : Fin (N + 1) → Ω) :
      π x * (P x (path 0) * pathWeight P N path) *
        (g x + observationSum g N path) ^ 2 =
      (π x * P x (path 0)) * pathWeight P N path * (g x) ^ 2 +
      2 * ((π x * g x * P x (path 0)) * pathWeight P N path * observationSum g N path) +
      (π x * P x (path 0)) * pathWeight P N path * (observationSum g N path) ^ 2 := by ring
  simp_rw [hexpand, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hfirst : (∑ x : Ω, ∑ path : Fin (N + 1) → Ω,
      (π x * P x (path 0)) * pathWeight P N path * (g x) ^ 2) = ip π g g := by
    change _ = ∑ x, π x * g x * g x
    apply Finset.sum_congr rfl
    intro x _
    rw [← Finset.sum_mul, path_mass P N (fun y => π x * P x y),
      ← Finset.mul_sum, P.sum_coe, mul_one]
    ring
  have hcross : (∑ x : Ω, ∑ path : Fin (N + 1) → Ω,
      (π x * g x * P x (path 0)) * pathWeight P N path * observationSum g N path) =
      ∑ t ∈ Finset.range N, ip π g ((P.iter (t + 1)).act g) := by
    rw [Finset.sum_congr rfl (fun x _ =>
      path_first_moment P g (fun y => π x * g x * P x y) N)]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    rw [FinKernel.act_iter_succ]
    change _ = ∑ x, π x * g x * ∑ y, P x y * (P.iter t).act g y
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    ring
  have hlast : (∑ x : Ω, ∑ path : Fin (N + 1) → Ω,
      (π x * P x (path 0)) * pathWeight P N path * (observationSum g N path) ^ 2) =
      ∑ path : Fin (N + 1) → Ω,
        π (path 0) * pathWeight P N path * (observationSum g N path) ^ 2 := by
    rw [Finset.sum_comm]
    simp only [← Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro path _
    rw [hst (path 0)]
  rw [hfirst, hcross, hlast]
  ring

/-- INTERNAL: A bound on all finite covariance sums bounds the stationary
second moment of N correlated observations.
TEXLINE: main.tex:1010-1013 -/
theorem stationary_square_le [DecidableEq Ω] (π : FinDist Ω)
    (P : FinChain Ω) (hst : Stationary π P) (g : Ω → ℝ) (C : ℝ)
    (hcov : ∀ N, (∑ t ∈ Finset.range N, ip π g ((P.iter t).act g)) ≤ C)
    (N : ℕ) : pathSquaredSum π P g N ≤ 2 * (N : ℝ) * C := by
  induction N with
  | zero => simp [pathSquaredSum, observationSum]
  | succ N ih =>
    rw [stationary_square_succ π P hst g N]
    have hc := hcov (N + 1)
    rw [Finset.sum_range_succ'] at hc
    simp only [FinKernel.iter_zero, FinKernel.act_id] at hc
    have hnonneg := ip_self_nonneg π g
    push_cast
    nlinarith

/-- INTERNAL: The finite product-path centered average has MSE at most
2C/N when every finite centered covariance sum is at most C.
TEXLINE: main.tex:1010-1013 -/
theorem stationary_average_le_of_covariance [DecidableEq Ω] (π : FinDist Ω)
    (P : FinChain Ω) (hst : Stationary π P) (G : Ω → ℝ) (C : ℝ)
    (hcov : ∀ N, (∑ t ∈ Finset.range N,
      ip π (fun x => G x - Ex π G)
        ((P.iter t).act (fun x => G x - Ex π G))) ≤ C)
    (N : ℕ) (hN : 0 < N) :
    (∑ path : Fin (N + 1) → Ω,
      (π (path 0) * ∏ i : Fin N, P (path i.castSucc) (path i.succ)) *
        ((∑ i : Fin N, G (path i.castSucc)) / (N : ℝ) - Ex π G) ^ 2) ≤
      2 * C / (N : ℝ) := by
  classical
  have hn : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  let g : Ω → ℝ := fun x => G x - Ex π G
  have hobs (path : Fin (N + 1) → Ω) :
      observationSum G N path / (N : ℝ) - Ex π G =
        observationSum g N path / (N : ℝ) := by
    simp only [observationSum, g, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  change (∑ path : Fin (N + 1) → Ω,
    (π (path 0) * pathWeight P N path) *
      (observationSum G N path / (N : ℝ) - Ex π G) ^ 2) ≤ _
  simp_rw [hobs, div_pow, ← mul_div_assoc]
  rw [← Finset.sum_div]
  change pathSquaredSum π P g N / (N : ℝ) ^ 2 ≤ _
  have hb := stationary_square_le π P hst g C hcov N
  have hden : (0 : ℝ) < (N : ℝ) ^ 2 := sq_pos_of_ne_zero hn
  apply (div_le_iff₀ hden).mpr
  have hr : (2 * C / (N : ℝ)) * (N : ℝ) ^ 2 = 2 * (N : ℝ) * C := by
    field_simp
  rw [hr]
  exact hb

end CountingMatroid.Analysis.StationaryPathMoment
