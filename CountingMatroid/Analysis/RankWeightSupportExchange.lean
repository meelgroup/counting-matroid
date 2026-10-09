import CountingMatroid.Analysis.LorentzianDirectionalSignature
import CountingMatroid.Analysis.BinaryRankWeightSignature

set_option autoImplicit false

/-! The subset exponent description of the rank-weight polynomial support.
The exchange condition depends only on the subsets, not on matroid ranks. -/

namespace CountingMatroid.Analysis.RankWeightSupportExchange

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: Encode a subset by its squarefree label exponents and the
remaining homogenizing degree. TEXLINE: main.tex:334-339 -/
noncomputable def subsetExponent {α : Type} [Fintype α] (A : Finset α) :
    Option α →₀ ℕ :=
  Finsupp.single none (Fintype.card α - A.card) +
    ∑ a ∈ A, Finsupp.single (some a) 1

/-- INTERNAL: The homogenizing coordinate records the complement cardinality. -/
theorem subsetExponent_none {α : Type} [Fintype α] (A : Finset α) :
    subsetExponent A none = Fintype.card α - A.card := by
  classical
  simp [subsetExponent]

/-- INTERNAL: Each label coordinate is the subset's membership indicator. -/
theorem subsetExponent_some {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset α) (a : α) : subsetExponent A (some a) = if a ∈ A then 1 else 0 := by
  classical
  simp [subsetExponent, Finsupp.single_apply, eq_comm]

/-- INTERNAL: Different subsets give different monomials. -/
theorem subsetExponent_injective {α : Type} [Fintype α] [DecidableEq α] :
    Function.Injective (subsetExponent (α := α)) := by
  intro A B h
  ext a
  have ha := congrArg (fun m => m (some a)) h
  simp only [subsetExponent_some] at ha
  by_cases hA : a ∈ A <;> by_cases hB : a ∈ B <;> simp_all

/-- INTERNAL: Each summand of the polynomial is a single encoded monomial. -/
theorem rank_weight_term_monomial {α : Type} [Fintype α] [DecidableEq α]
    (A : Finset α) (c : ℚ) :
    MvPolynomial.C c * MvPolynomial.X none ^ (Fintype.card α - A.card) *
      (∏ a ∈ A, MvPolynomial.X (some a)) =
      MvPolynomial.monomial (subsetExponent A) c := by
  rw [MvPolynomial.C_mul_X_pow_eq_monomial]
  have hprod : (∏ a ∈ A, MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ) =
      MvPolynomial.monomial (∑ a ∈ A, Finsupp.single (some a) 1) 1 := by
    rw [MvPolynomial.monomial_sum_one]
    rfl
  rw [hprod, MvPolynomial.monomial_mul, mul_one]
  rfl

/-- INTERNAL: Nonzero rank weights leave exactly all subset exponents in the
polynomial support. TEXLINE: main.tex:334-339 -/
theorem rank_weight_mem_support_iff {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (m : Option α →₀ ℕ) :
    m ∈ (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)).support ↔
      ∃ A : Finset α, m = subsetExponent A := by
  classical
  simp_rw [rank_weight_term_monomial]
  constructor
  · intro hm
    obtain ⟨A, _, hA⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hm)
    have hne : (q ^ (N.eRk (A : Set α)).toNat)⁻¹ ≠ 0 :=
      ne_of_gt (inv_pos.mpr (pow_pos hq _))
    rw [MvPolynomial.support_monomial, if_neg hne, Finset.mem_singleton] at hA
    exact ⟨A, hA⟩
  · rintro ⟨A, rfl⟩
    rw [MvPolynomial.mem_support_iff, MvPolynomial.coeff_sum]
    simp only [MvPolynomial.coeff_monomial]
    have hinj := subsetExponent_injective (α := α)
    simp only [hinj.eq_iff]
    simpa using ne_of_gt (inv_pos.mpr (pow_pos hq (N.eRk (A : Set α)).toNat))

/-- INTERNAL: The full subset support admits transfer of a unit from a larger
coordinate to a smaller one. TEXLINE: main.tex:334-339 -/
theorem rank_weight_support_exchange {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) :
    HasMConvexSupport (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)) := by
  classical
  intro x hx y hy i hi
  obtain ⟨A, rfl⟩ := (rank_weight_mem_support_iff N q hq x).mp hx
  obtain ⟨B, rfl⟩ := (rank_weight_mem_support_iff N q hq y).mp hy
  cases i with
  | none =>
    simp only [subsetExponent_none] at hi
    have hAB : A.card < B.card := by omega
    obtain ⟨b, hbB, hbA⟩ := Finset.exists_mem_notMem_of_card_lt_card hAB
    refine ⟨some b, ?_, ?_⟩
    · simp [subsetExponent_some, hbA, hbB]
    · apply (rank_weight_mem_support_iff N q hq _).mpr
      refine ⟨insert b A, ?_⟩
      ext s
      cases s with
      | none =>
        have hbound := (insert b A).card_le_univ
        rw [Finset.card_insert_of_notMem hbA] at hbound
        simp [subsetExponent_none,
          Finset.card_insert_of_notMem hbA]
        omega
      | some c =>
        by_cases hcb : c = b
        · subst c; simp [subsetExponent_some, hbA]
        · simp [subsetExponent_some, hcb]
  | some a =>
    simp only [subsetExponent_some] at hi
    have haA : a ∈ A := by split_ifs at hi <;> omega
    have haB : a ∉ B := by split_ifs at hi <;> omega
    by_cases hnone : subsetExponent A none < subsetExponent B none
    · refine ⟨none, hnone, ?_⟩
      apply (rank_weight_mem_support_iff N q hq _).mpr
      refine ⟨A.erase a, ?_⟩
      ext s
      cases s with
      | none =>
        have hbound := A.card_le_univ
        have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, haA⟩)
        simp [subsetExponent_none, Finset.card_erase_of_mem haA]
        omega
      | some c =>
        by_cases hca : c = a
        · subst c; simp [subsetExponent_some, haA]
        · simp [subsetExponent_some, hca]
    · have hAB : A.card ≤ B.card := by
        simp only [subsetExponent_none] at hnone
        have hA := A.card_le_univ
        have hB := B.card_le_univ
        omega
      have hlt : (A.erase a).card < B.card := by
        rw [Finset.card_erase_of_mem haA]
        have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, haA⟩)
        omega
      obtain ⟨b, hbB, hbErase⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
      have hba : b ≠ a := by intro h; subst b; exact haB hbB
      have hbA : b ∉ A := by
        intro hb
        exact hbErase (Finset.mem_erase.mpr ⟨hba, hb⟩)
      refine ⟨some b, ?_, ?_⟩
      · simp [subsetExponent_some, hbA, hbB]
      · apply (rank_weight_mem_support_iff N q hq _).mpr
        refine ⟨insert b (A.erase a), ?_⟩
        ext s
        cases s with
        | none =>
          have hpos := Finset.card_pos.mpr (show A.Nonempty from ⟨a, haA⟩)
          simp [subsetExponent_none,
            Finset.card_insert_of_notMem hbErase, Finset.card_erase_of_mem haA]
          omega
        | some c =>
          by_cases hca : c = a <;> by_cases hcb : c = b <;>
            simp_all [subsetExponent_some, Finsupp.single_apply, eq_comm]

end CountingMatroid.Analysis.RankWeightSupportExchange

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · identified the support with all subset exponents and proved unit exchange by insert, erase, and swap; the argument needs only positive coefficients and no matroid exchange or rank-signature theorem.
-/
