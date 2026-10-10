import CountingMatroid.Analysis.PositiveTimeTraceKernel

set_option autoImplicit false

/-!
Capped positive-time returns started from the stationary law restricted to
the target never put more mass on a target state than the stationary law
does. Iterating, any start dominated by a multiple of the restricted
stationary law stays dominated through every number of capped returns.
Lost (capped) mass is retained as a deficit, not renormalised.
-/
namespace CountingMatroid.Analysis.CappedReturnSubstationary

open Arlib.Probability Arlib.MarkovChains
open CountingMatroid.Analysis.PositiveTimeTraceKernel

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Mass flowing through off-target states, one underlying step at a
time, killed as soon as it reaches the target.
TEXLINE: main.tex:1072-1087 -/
noncomputable def killedFlow (P : FinChain Ω) (A : Finset Ω) (lam : Ω → ℝ) :
    ℕ → Ω → ℝ
  | 0 => lam
  | s + 1 => fun w => ∑ z, (if z ∈ A then 0 else killedFlow P A lam s z) * P z w

/-- INTERNAL: Starting the flow one step later shifts its index. -/
theorem killed_flow_shift (P : FinChain Ω) (A : Finset Ω) (lam : Ω → ℝ) (s : ℕ) :
    killedFlow P A (killedFlow P A lam 1) s = killedFlow P A lam (s + 1) := by
  induction s with
  | zero => rfl
  | succ s ih =>
      funext w
      simp only [killedFlow] at ih ⊢
      rw [ih]

/-- INTERNAL: The mass hitting a target state within k steps is the total
flow arriving there at times 0,…,k.
TEXLINE: main.tex:1072-1087 -/
theorem hit_within_flow (P : FinChain Ω) (A : Finset Ω) (k : ℕ) (lam : Ω → ℝ)
    (x : Ω) (hx : x ∈ A) :
    (∑ z, lam z * (hitWithin P A k).entry z x) =
      ∑ s ∈ Finset.range (k + 1), killedFlow P A lam s x := by
  induction k generalizing lam with
  | zero =>
      simp only [hitWithin, targetIdentity, zero_add, Finset.range_one,
        Finset.sum_singleton, killedFlow]
      rw [Finset.sum_eq_single x]
      · simp [hx]
      · intro z _ hz
        simp [hz]
      · simp
  | succ k ih =>
      have hsplit (z : Ω) : lam z * (hitWithin P A (k + 1)).entry z x =
          (if z = x then lam z else 0) +
            ∑ w, ((if z ∈ A then 0 else lam z) * P z w) *
              (hitWithin P A k).entry w x := by
        by_cases hz : z ∈ A
        · rw [hitWithin_on_target P A (k + 1) z x hz]
          by_cases hzx : z = x
          · subst hzx
            simp [hz]
          · simp [hz, hzx]
        · have hzx : z ≠ x := fun h => hz (h ▸ hx)
          simp only [hitWithin, hz, if_false, compose, ofChain, hzx, zero_add]
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro w _
          ring
      simp_rw [hsplit, Finset.sum_add_distrib]
      rw [Finset.sum_ite_eq' Finset.univ x, if_pos (Finset.mem_univ x)]
      rw [Finset.sum_comm]
      simp_rw [← Finset.sum_mul]
      have hflow := ih (killedFlow P A lam 1)
      simp only [killedFlow] at hflow
      rw [hflow, Finset.sum_range_succ' _ (k + 1)]
      simp only [killedFlow]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro s _
      have h := killed_flow_shift P A lam s
      simp only [killedFlow] at h
      exact congrFun h x

/-- INTERNAL: Flow started from the one-step image of the restricted
stationary law never exceeds the stationary law, cumulatively in time.
TEXLINE: main.tex:1072-1087 -/
theorem killed_flow_le (P : FinChain Ω) (A : Finset Ω) (μ : FinDist Ω)
    (hμ : Stationary μ P) (t : ℕ) (w : Ω) :
    (∑ s ∈ Finset.range (t + 1), killedFlow P A
      (fun w => ∑ z, (if z ∈ A then μ z else 0) * P z w) s w) ≤ μ w := by
  induction t generalizing w with
  | zero =>
      simp only [zero_add, Finset.range_one, Finset.sum_singleton, killedFlow]
      rw [← hμ w]
      apply Finset.sum_le_sum
      intro z _
      apply mul_le_mul_of_nonneg_right _ (P.coe_nonneg z w)
      split_ifs
      · exact le_rfl
      · exact μ.coe_nonneg z
  | succ t ih =>
      rw [Finset.sum_range_succ']
      simp only [killedFlow]
      have hswap : (∑ s ∈ Finset.range (t + 1), ∑ z, (if z ∈ A then 0 else
          killedFlow P A (fun w => ∑ z, (if z ∈ A then μ z else 0) * P z w) s z) *
            P z w) =
          ∑ z, (if z ∈ A then 0 else ∑ s ∈ Finset.range (t + 1),
            killedFlow P A (fun w => ∑ z, (if z ∈ A then μ z else 0) * P z w) s z) *
              P z w := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro z _
        rw [← Finset.sum_mul]
        congr 1
        split_ifs <;> simp
      rw [hswap, ← Finset.sum_add_distrib, ← hμ w]
      apply Finset.sum_le_sum
      intro z _
      by_cases hz : z ∈ A
      · simp [hz]
      · simp only [hz, if_false, zero_mul, add_zero]
        exact mul_le_mul_of_nonneg_right (ih z) (P.coe_nonneg z w)

/-- INTERNAL: Capped positive-time returns from the restricted stationary law
are sub-stationary on the target.
TEXLINE: main.tex:1072-1087,1226-1229 -/
theorem return_within_substationary (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hμ : Stationary μ P) (k : ℕ) (x : Ω) :
    (∑ y, (if y ∈ A then μ y else 0) * (returnWithin P A k).entry y x) ≤
      if x ∈ A then μ x else 0 := by
  by_cases hx : x ∈ A
  · rw [if_pos hx]
    cases k with
    | zero =>
        simp only [returnWithin, mul_zero, Finset.sum_const_zero]
        exact μ.coe_nonneg x
    | succ k =>
        simp only [returnWithin, compose, ofChain]
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        simp_rw [← mul_assoc, ← Finset.sum_mul]
        rw [hit_within_flow P A k _ x hx]
        exact killed_flow_le P A μ hμ k x
  · rw [if_neg hx]
    simp [returnWithin_supported P A k _ x hx]

/-- INTERNAL: A start dominated by a multiple of the restricted stationary
law stays so dominated through any number of capped returns.
TEXLINE: main.tex:1226-1229 -/
theorem iterate_return_substationary (P : FinChain Ω) (A : Finset Ω)
    (μ : FinDist Ω) (hμ : Stationary μ P) (k : ℕ) (c : ℝ) (hc : 0 ≤ c)
    (lam : Ω → ℝ) (hlam0 : ∀ y, 0 ≤ lam y)
    (hlam : ∀ y, lam y ≤ c * (if y ∈ A then μ y else 0)) (steps : ℕ) (x : Ω) :
    (∑ y, lam y * (iterate (returnWithin P A k) steps).entry y x) ≤
      c * (if x ∈ A then μ x else 0) := by
  induction steps generalizing lam with
  | zero =>
      simp only [iterate, identity]
      rw [Finset.sum_eq_single x]
      · simpa using hlam x
      · intro y _ hy
        simp [hy]
      · simp
  | succ steps ih =>
      simp only [iterate, compose]
      simp_rw [Finset.mul_sum]
      rw [Finset.sum_comm]
      simp_rw [← mul_assoc, ← Finset.sum_mul]
      apply ih
      · intro z
        exact Finset.sum_nonneg fun y _ =>
          mul_nonneg (hlam0 y) ((returnWithin P A k).nonneg y z)
      · intro z
        calc
          (∑ y, lam y * (returnWithin P A k).entry y z) ≤
              ∑ y, (c * (if y ∈ A then μ y else 0)) * (returnWithin P A k).entry y z :=
            Finset.sum_le_sum fun y _ =>
              mul_le_mul_of_nonneg_right (hlam y) ((returnWithin P A k).nonneg y z)
          _ = c * ∑ y, (if y ∈ A then μ y else 0) * (returnWithin P A k).entry y z := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro y _
            ring
          _ ≤ c * (if z ∈ A then μ z else 0) :=
            mul_le_mul_of_nonneg_left (return_within_substationary P A μ hμ k z) hc

end CountingMatroid.Analysis.CappedReturnSubstationary

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · killed-flow decomposition of finite hitting, cumulative flow bound by stationarity, capped-return sub-stationarity and its iterated domination form.
-/
