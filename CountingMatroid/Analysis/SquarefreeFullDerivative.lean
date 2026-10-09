import CountingMatroid.Analysis.RankWeightSupportExchange

set_option autoImplicit false

/-! Coefficient extraction for full coordinate derivatives of squarefree-label
homogenizations. The coefficient multiplier counts repeated homogenizer
coordinates while the label coordinates are distinct. -/

namespace CountingMatroid.Analysis.SquarefreeFullDerivative

open scoped BigOperators
open RankWeightSupportExchange

/-- INTERNAL: Extract a coefficient after distinct label derivatives and any
number of homogenizer derivatives. The queried coefficient has zero exponent
at each differentiated label. -/
theorem squarefree_fold_coeff {α : Type} [DecidableEq α]
    (xs : List (Option α)) (p : MvPolynomial (Option α) ℚ)
    (m : Option α →₀ ℕ) (hnd : (xs.filterMap id).Nodup)
    (hm : ∀ a ∈ xs.filterMap id, m (some a) = 0) :
    (xs.foldr (fun s f => MvPolynomial.pderiv s f) p).coeff m =
      p.coeff (m + (Finsupp.single none (xs.count none) +
        ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1)) *
        ((m none + 1).ascFactorial (xs.count none) : ℚ) := by
  classical
  induction xs generalizing m with
  | nil => simp
  | cons s xs ih =>
    rw [List.foldr_cons, MvPolynomial.coeff_pderiv]
    cases s with
    | none =>
      have hm' : ∀ a ∈ xs.filterMap id, (m + Finsupp.single none 1 : Option α →₀ ℕ) (some a) = 0 := by
        simpa using hm
      rw [ih _ (by simpa using hnd) hm']
      have hexp : m + Finsupp.single none 1 +
          (Finsupp.single none (xs.count none) +
            ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1) =
          m + (Finsupp.single none ((none :: xs).count none) +
            ∑ a ∈ ((none :: xs).filterMap id).toFinset, Finsupp.single (some a) 1) := by
        simp only [List.count_cons_self, List.filterMap_cons, id_eq]
        rw [Finsupp.single_add]
        abel
      rw [hexp]
      simp only [List.count_cons_self, List.filterMap_cons, id_eq, Finsupp.add_apply,
        Finsupp.single_eq_same]
      have hf := Nat.succ_ascFactorial (m none + 1) (xs.count none)
      rw [← Nat.ascFactorial_succ] at hf
      have hfq := congrArg (fun n : ℕ => (n : ℚ)) hf
      push_cast at hfq
      simp only [Nat.succ_eq_add_one] at hfq
      calc
        _ = p.coeff _ * ((↑(m none) + 1) * ↑((m none + 1 + 1).ascFactorial (xs.count none))) := by ring
        _ = _ := by rw [hfq]
    | some a =>
      have hnd' : a ∉ xs.filterMap id ∧ (xs.filterMap id).Nodup := by simpa using hnd
      have hma : m (some a) = 0 := hm a (by simp)
      have hm' : ∀ b ∈ xs.filterMap id, (m + Finsupp.single (some a) 1 : Option α →₀ ℕ) (some b) = 0 := by
        intro b hb
        have hba : b ≠ a := by intro h; subst b; exact hnd'.1 hb
        simpa [Finsupp.single_apply, hba, Ne.symm hba] using hm b (by simpa only [List.filterMap_cons, id_eq] using List.mem_cons_of_mem a hb)
      rw [ih _ hnd'.2 hm']
      have hexp : m + Finsupp.single (some a) 1 +
          (Finsupp.single none (xs.count none) +
            ∑ b ∈ (xs.filterMap id).toFinset, Finsupp.single (some b) 1) =
          m + (Finsupp.single none (((some a) :: xs).count none) +
            ∑ b ∈ (((some a) :: xs).filterMap id).toFinset, Finsupp.single (some b) 1) := by
        simp only [List.count_cons_of_ne (Option.some_ne_none a), List.filterMap_cons, id_eq,
          List.toFinset_cons]
        rw [Finset.sum_insert (by simpa using hnd'.1)]
        abel
      rw [hexp]
      simp [hma]

/-- INTERNAL: The encoded subset monomial has exactly its assigned weight,
since different subsets have different encoded exponents. -/
theorem squarefree_homogenization_coeff {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (S : Finset α) :
    (∑ A : Finset α, MvPolynomial.C (w A) *
      MvPolynomial.X none ^ (Fintype.card α - A.card) *
        ∏ a ∈ A, MvPolynomial.X (some a)).coeff (subsetExponent S) = w S := by
  classical
  simp_rw [rank_weight_term_monomial]
  rw [MvPolynomial.coeff_sum]
  simp only [MvPolynomial.coeff_monomial, subsetExponent_injective.eq_iff]
  simp

/-- INTERNAL: A full coordinate derivative with distinct labels extracts the
weight of their set, multiplied by the factorial of the homogenizer count.
TEXLINE: main.tex:334-348 -/
theorem squarefree_full_derivative {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α))
    (hnd : (xs.filterMap id).Nodup) (hlen : xs.length = Fintype.card α) :
    MvPolynomial.constantCoeff
      (xs.foldr (fun s f => MvPolynomial.pderiv s f)
        (∑ A : Finset α, MvPolynomial.C (w A) *
          MvPolynomial.X none ^ (Fintype.card α - A.card) *
            ∏ a ∈ A, MvPolynomial.X (some a))) =
      w (xs.filterMap id).toFinset * (Nat.factorial (xs.count none) : ℚ) := by
  classical
  rw [MvPolynomial.constantCoeff_eq]
  rw [squarefree_fold_coeff xs _ 0 hnd (by simp)]
  have hcount (ys : List (Option α)) : ys.count none + (ys.filterMap id).length = ys.length := by
    induction ys with
    | nil => simp
    | cons s xs ih => cases s <;> simp at * <;> omega
  have he : Finsupp.single none (xs.count none) +
      ∑ a ∈ (xs.filterMap id).toFinset, Finsupp.single (some a) 1 =
      subsetExponent (xs.filterMap id).toFinset := by
    unfold subsetExponent
    rw [List.toFinset_card_of_nodup hnd]
    rw [show Fintype.card α - (xs.filterMap id).length = xs.count none by have hc := hcount xs; omega]
  simp only [zero_add, Finsupp.zero_apply, Nat.one_ascFactorial, he,
    squarefree_homogenization_coeff]

end CountingMatroid.Analysis.SquarefreeFullDerivative

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · extracted coefficients through distinct label derivatives with an ascending-factorial homogenizer multiplier, then identified full derivatives with the selected subset weight times the homogenizer factorial.
-/
