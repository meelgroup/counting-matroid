import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic.Positivity

set_option autoImplicit false

/-!
Support calculations for a nonnegative directional derivative. Its coefficients
are nonnegative, and its support consists precisely of exponents obtained by
removing a unit in a direction with positive weight. The exchange condition
is preserved by a finite exchange argument on these lifted exponents.
-/

namespace CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

open scoped BigOperators

/-- INTERNAL: Nonnegative directional differentiation has no coefficient cancellation.
TEXLINE: main.tex:340-348 -/
theorem directional_coeff_nonnegative {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : ∀ m, 0 ≤ p.coeff m)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) (m : σ →₀ ℕ) :
    0 ≤ (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p).coeff m := by
  classical
  rw [MvPolynomial.coeff_sum]
  apply Finset.sum_nonneg
  intro s _
  rw [MvPolynomial.coeff_C_mul, MvPolynomial.coeff_pderiv]
  exact mul_nonneg (hd s) (mul_nonneg (hp _) (by positivity))

/-- INTERNAL: The support of a directional derivative is a weighted union of
unit deletions, with no cancellation because all coefficients are nonnegative.
TEXLINE: main.tex:340-348 -/
theorem mem_directional_support_iff {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : ∀ m, 0 ≤ p.coeff m)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) (m : σ →₀ ℕ) :
    m ∈ (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p).support ↔
      ∃ s, 0 < d s ∧ m + Finsupp.single s 1 ∈ p.support := by
  classical
  rw [MvPolynomial.mem_support_iff]
  have hnonneg := directional_coeff_nonnegative p hp d hd m
  rw [ne_comm, ne_iff_lt_iff_le.mpr hnonneg]
  simp only [MvPolynomial.coeff_sum, MvPolynomial.coeff_C_mul,
    MvPolynomial.coeff_pderiv]
  rw [Finset.sum_pos_iff_of_nonneg (fun s _ =>
    mul_nonneg (hd s) (mul_nonneg (hp _) (by positivity)))]
  simp only [Finset.mem_univ, true_and]
  apply exists_congr
  intro s
  have hnat : (0 : ℚ) < (m s : ℚ) + 1 := by positivity
  rw [← mul_assoc, mul_pos_iff_of_pos_right hnat]
  rw [mul_pos_iff]
  have hdnot : ¬ d s < 0 := not_lt.mpr (hd s)
  simp only [hdnot, false_and, or_false, MvPolynomial.mem_support_iff]
  rw [ne_comm, ne_iff_lt_iff_le.mpr (hp _)]

/-- INTERNAL: Unit deletion in any nonnegative direction preserves the
M-convex exchange condition of a homogeneous nonnegative polynomial.
The combinatorial argument uses only the exchange condition; the homogeneous
hypothesis is retained in the stated interface.
TEXLINE: main.tex:340-348 -/
theorem nonnegative_directional_mconvex_support {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hhom : p.IsHomogeneous n)
    (hp : ∀ m, 0 ≤ p.coeff m)
    (hex : ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support)
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    let q := ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p
    ∀ x ∈ q.support, ∀ y ∈ q.support, ∀ i, y i < x i →
      ∃ j, x j < y j ∧
        x - Finsupp.single i 1 + Finsupp.single j 1 ∈ q.support := by
  classical
  have hswap (x : σ →₀ ℕ) (i a j : σ) (hxi : 0 < x i) :
      (x + Finsupp.single a 1) - Finsupp.single i 1 + Finsupp.single j 1 =
        (x - Finsupp.single i 1 + Finsupp.single j 1) + Finsupp.single a 1 := by
    ext t
    by_cases hit : i = t
    · subst t
      simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
      split_ifs <;> omega
    · simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply, hit,
        add_comm, add_left_comm]
  intro q x hx y hy i hi
  obtain ⟨a, ha, hxa⟩ := (mem_directional_support_iff p hp d hd x).mp hx
  obtain ⟨b, hb, hyb⟩ := (mem_directional_support_iff p hp d hd y).mp hy
  have hxi : 0 < x i := by omega
  -- First try exchange at the requested coordinate in the lifted support.
  by_cases hlift : (y + Finsupp.single b 1 : σ →₀ ℕ) i <
      (x + Finsupp.single a 1 : σ →₀ ℕ) i
  · obtain ⟨j, hj, hmem⟩ := hex _ hxa _ hyb i hlift
    rw [hswap x i a j hxi] at hmem
    by_cases hjDef : x j < y j
    · exact ⟨j, hjDef,
        (mem_directional_support_iff p hp d hd _).mpr ⟨a, ha, hmem⟩⟩
    · have hjb : j = b := by
        by_contra hjb
        simp [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hjb] at hj
        omega
      subst j
      have hab : a ≠ b := by
        intro hab
        subst a
        simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hj
        omega
      have hbi : b ≠ i := by
        intro hbi
        subst b
        omega
      -- The exchange reached the extra unit at b. Delete at b when a is
      -- already a deficit; otherwise exchange once more at a.
      by_cases haDef : x a < y a
      · refine ⟨a, haDef,
          (mem_directional_support_iff p hp d hd _).mpr ⟨b, hb, ?_⟩⟩
        simpa only [add_assoc, add_comm, add_left_comm] using hmem
      · have haLift : (y + Finsupp.single b 1 : σ →₀ ℕ) a <
            ((x - Finsupp.single i 1 + Finsupp.single b 1) +
              Finsupp.single a 1 : σ →₀ ℕ) a := by
          simp only [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply]
          split_ifs <;> simp_all only [not_lt] <;> omega
        obtain ⟨k, hk, hmem2⟩ := hex _ hmem _ hyb a haLift
        rw [add_tsub_cancel_right] at hmem2
        by_cases hkDef : x k < y k
        · refine ⟨k, hkDef,
            (mem_directional_support_iff p hp d hd _).mpr ⟨b, hb, ?_⟩⟩
          simpa only [add_assoc, add_comm, add_left_comm] using hmem2
        · have hki : k = i := by
            by_contra hki
            simp [Finsupp.add_apply, Finsupp.tsub_apply, Finsupp.single_apply,
              Ne.symm hki] at hk
            omega
          subst k
          rw [add_right_comm, Finsupp.sub_add_single_one_cancel
            (by omega : x i ≠ 0)] at hmem2
          have hiLift : (y + Finsupp.single b 1 : σ →₀ ℕ) i <
              (x + Finsupp.single b 1 : σ →₀ ℕ) i := by
            simp only [Finsupp.add_apply]
            omega
          obtain ⟨k, hk, hmem3⟩ := hex _ hmem2 _ hyb i hiLift
          have hkDef : x k < y k := by
            simp only [Finsupp.add_apply] at hk
            omega
          rw [hswap x i b k hxi] at hmem3
          exact ⟨k, hkDef,
            (mem_directional_support_iff p hp d hd _).mpr ⟨b, hb, hmem3⟩⟩
  -- If the lift hides the deficit, b = i. Deleting that unit either
  -- immediately exchanges toward a or allows an exchange starting at a.
  · have hbi : b = i := by
      by_contra hbi
      simp [Finsupp.add_apply, Finsupp.single_apply, hbi] at hlift
      omega
    subst b
    by_cases hai : a = i
    · subst a
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hlift
      omega
    by_cases haDef : x a < y a
    · refine ⟨a, haDef, (mem_directional_support_iff p hp d hd _).mpr ⟨i, hb, ?_⟩⟩
      have heq : (x - Finsupp.single i 1 + Finsupp.single a 1) +
          Finsupp.single i 1 = x + Finsupp.single a 1 := by
        rw [add_right_comm, Finsupp.sub_add_single_one_cancel (by omega : x i ≠ 0)]
      rw [heq]
      exact hxa
    · have haLift : (y + Finsupp.single i 1 : σ →₀ ℕ) a <
          (x + Finsupp.single a 1 : σ →₀ ℕ) a := by
        simp [Finsupp.add_apply, Ne.symm hai]
        omega
      obtain ⟨j, hj, hmem⟩ := hex _ hxa _ hyb a haLift
      have hji : j ≠ i := by
        intro hji
        subst j
        simp [Finsupp.add_apply, hai] at hj hlift
        omega
      have hjDef : x j < y j := by
        simp [Finsupp.add_apply, Finsupp.single_apply, Ne.symm hji] at hj
        omega
      have hcancel : (x + Finsupp.single a 1) - Finsupp.single a 1 = x :=
        add_tsub_cancel_right _ _
      rw [hcancel] at hmem
      refine ⟨j, hjDef, (mem_directional_support_iff p hp d hd _).mpr ⟨i, hb, ?_⟩⟩
      rw [add_right_comm, Finsupp.sub_add_single_one_cancel (by omega : x i ≠ 0)]
      exact hmem

end CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed directional support exchange by lifting support witnesses and using at most three original-support exchanges; no new proof obligations.
-/
