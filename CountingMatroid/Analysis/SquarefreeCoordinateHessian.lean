import CountingMatroid.Analysis.RankWeightSupportExchange
import CountingMatroid.Analysis.SquarefreeFullDerivative

set_option autoImplicit false

/-! Coordinate differentiation of a homogeneous polynomial whose label
variables are squarefree reduces its constant Hessian to a residual matrix.
The matrix records the selected labels and the number of homogenizer
derivatives. This calculation concerns arbitrary subset coefficients and
does not assume a matroid signature bound. -/

namespace CountingMatroid.Analysis.SquarefreeCoordinateHessian

open scoped BigOperators
open LorentzianDirectionalSignature

/-- INTERNAL: The residual Hessian before multiplication by the factorial of
the number of homogenizer derivatives. Selected label rows are zero.
TEXLINE: main.tex:334-339 -/
noncomputable def squarefreeResidualHessian {α : Type} [DecidableEq α]
    (w : Finset α → ℚ) (S : Finset α) (k : ℕ) :
    Matrix (Option α) (Option α) ℝ := fun i j =>
  match i, j with
  | none, none => (k + 2 : ℝ) * (k + 1 : ℝ) * (w S : ℝ)
  | none, some a => if a ∈ S then 0 else (k + 1 : ℝ) * (w (insert a S) : ℝ)
  | some a, none => if a ∈ S then 0 else (k + 1 : ℝ) * (w (insert a S) : ℝ)
  | some a, some b =>
      if a ∈ S ∨ b ∈ S ∨ a = b then 0 else (w (insert a (insert b S)) : ℝ)

/-- INTERNAL: Separate homogenizer derivatives from the list of label
derivatives without losing multiplicity. -/
theorem option_list_length {α : Type} [DecidableEq α] (xs : List (Option α)) :
    xs.count none + (xs.filterMap id).length = xs.length := by
  induction xs with
  | nil => simp
  | cons s xs ih =>
    cases s <;> simp at * <;> omega

/-- INTERNAL: A coordinate derivative commutes through a list of coordinate
derivatives, allowing a monomial induction to differentiate its input first. -/
theorem coordinate_fold_pderiv_commute {σ : Type} (xs : List σ) (s : σ)
    (p : MvPolynomial σ ℚ) :
    MvPolynomial.pderiv s (xs.foldr (fun t f => MvPolynomial.pderiv t f) p) =
      xs.foldr (fun t f => MvPolynomial.pderiv t f) (MvPolynomial.pderiv s p) := by
  induction xs with
  | nil => rfl
  | cons t xs ih =>
    simp only [List.foldr_cons]
    rw [coordinate_pderiv_commute, ih]

/-- INTERNAL: Too many coordinate derivatives annihilate a monomial, even
when derivatives in other coordinates separate the repeated ones. -/
theorem coordinate_monomial_zero_of_count {σ : Type} [DecidableEq σ]
    [BEq σ] [LawfulBEq σ]
    (xs : List σ) (a : σ) (m : σ →₀ ℕ) (c : ℚ) (h : m a < xs.count a) :
    xs.foldr (fun t f => MvPolynomial.pderiv t f) (MvPolynomial.monomial m c) = 0 := by
  have hz : ∀ ys : List σ,
      ys.foldr (fun t f => MvPolynomial.pderiv t f) (0 : MvPolynomial σ ℚ) = 0 := by
    intro ys
    induction ys with
    | nil => rfl
    | cons t ys ih => simp [ih]
  induction xs generalizing m c with
  | nil => simp at h
  | cons s xs ih =>
    rw [List.foldr_cons, coordinate_fold_pderiv_commute, MvPolynomial.pderiv_monomial]
    by_cases hs : m s = 0
    · simpa [hs] using hz xs
    · apply ih
      by_cases hsa : s = a
      · subst s
        simp only [List.count_cons_self, Finsupp.tsub_apply, Finsupp.single_eq_same] at *
        omega
      · simpa [List.count_cons, Finsupp.tsub_apply, Finsupp.single_apply,
          hsa, Ne.symm hsa] using h

/-- INTERNAL: A repeated label derivative annihilates the entire squarefree
homogenization, independently of the homogenizer derivatives. -/
theorem squarefree_fold_zero_of_not_nodup {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α)) (hnd : ¬ (xs.filterMap id).Nodup) :
    xs.foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ A : Finset α, MvPolynomial.C (w A) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)) = 0 := by
  classical
  have hcount (ys : List (Option α)) (a : α) :
      (ys.filterMap id).count a = ys.count (some a) := by
    induction ys with
    | nil => rfl
    | cons s ys ih => cases s <;> simpa [List.count_cons] using ih
  rw [List.nodup_iff_count_le_one] at hnd
  push_neg at hnd
  obtain ⟨a, ha⟩ := hnd
  rw [hcount] at ha
  have hsum (ys : List (Option α)) (f : Finset α → MvPolynomial (Option α) ℚ) :
      ys.foldr (fun s p => MvPolynomial.pderiv s p) (∑ A, f A) =
        ∑ A, ys.foldr (fun s p => MvPolynomial.pderiv s p) (f A) := by
    induction ys with
    | nil => rfl
    | cons s ys ih => simp only [List.foldr_cons, ih, map_sum]
  rw [hsum]
  apply Finset.sum_eq_zero
  intro A _
  rw [RankWeightSupportExchange.rank_weight_term_monomial]
  apply coordinate_monomial_zero_of_count xs (some a)
  rw [RankWeightSupportExchange.subsetExponent_some]
  split_ifs <;> omega

/-- INTERNAL: Every quadratic coordinate descendant of a squarefree-label
homogenization is a nonnegative scalar multiple of its explicit residual
Hessian. Repeated label derivatives give the zero scalar. For distinct labels
the witnesses are their set, the count of `none`, and that count's factorial.
This identity holds for arbitrary rational subset coefficients.
TEXLINE: main.tex:334-348 -/
theorem squarefree_coordinate_hessian {α : Type} [Fintype α] [DecidableEq α]
    (w : Finset α → ℚ) (xs : List (Option α))
    (hlength : xs.length + 2 = Fintype.card α) :
    ∃ (S : Finset α) (k : ℕ) (c : ℝ),
      0 ≤ c ∧ S.card + k + 2 = Fintype.card α ∧
      constantHessianForm
        (xs.foldr (fun s f => MvPolynomial.pderiv s f)
          (∑ A : Finset α,
            MvPolynomial.C (w A) *
              MvPolynomial.X none ^ (Fintype.card α - A.card) *
                ∏ a ∈ A, MvPolynomial.X (some a))) =
        c • (squarefreeResidualHessian w S k).toQuadraticForm' := by
  classical
  by_cases hnd : (xs.filterMap id).Nodup
  · refine ⟨(xs.filterMap id).toFinset, xs.count none,
      (Nat.factorial (xs.count none) : ℝ), by positivity, ?_, ?_⟩
    · rw [List.toFinset_card_of_nodup hnd]
      have hlen := option_list_length xs
      omega
    · have hfull (i j : Option α) (hn : ((i :: j :: xs).filterMap id).Nodup) :
          MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) =
          w ((i :: j :: xs).filterMap id).toFinset *
            (Nat.factorial ((i :: j :: xs).count none) : ℚ) := by
        exact SquarefreeFullDerivative.squarefree_full_derivative w (i :: j :: xs) hn
          (by simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hlength)
      have hzero (i j : Option α) (hn : ¬ ((i :: j :: xs).filterMap id).Nodup) :
          MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) = 0 := by
        change MvPolynomial.constantCoeff ((i :: j :: xs).foldr _ _) = 0
        rw [squarefree_fold_zero_of_not_nodup w (i :: j :: xs) hn, map_zero]
      have hentry (i j : Option α) :
          ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) : ℚ) : ℝ) =
          (Nat.factorial (xs.count none) : ℝ) *
            squarefreeResidualHessian w (xs.filterMap id).toFinset (xs.count none) i j := by
        cases i with
        | none =>
          cases j with
          | none =>
            rw [hfull none none (by simpa using hnd)]
            simp [squarefreeResidualHessian, Nat.factorial_succ]
            ring
          | some a =>
            by_cases ha : some a ∈ xs
            · rw [hzero none (some a) (by simp [ha])]
              simp [squarefreeResidualHessian, ha]
            · rw [hfull none (some a) (by simpa [ha] using hnd)]
              simp [squarefreeResidualHessian, ha, Nat.factorial_succ]
              ring
        | some a =>
          cases j with
          | none =>
            by_cases ha : some a ∈ xs
            · rw [hzero (some a) none (by simp [ha])]
              simp [squarefreeResidualHessian, ha]
            · rw [hfull (some a) none (by simpa [ha] using hnd)]
              simp [squarefreeResidualHessian, ha, Nat.factorial_succ]
              ring
          | some b =>
            by_cases hab : some a ∈ xs ∨ some b ∈ xs ∨ a = b
            · rw [hzero (some a) (some b) (by
                simp only [List.filterMap_cons, id_eq, List.nodup_cons, List.mem_cons]
                simp only [List.mem_filterMap, exists_eq_right] at *
                tauto)]
              simp [squarefreeResidualHessian, hab]
            · have ha : some a ∉ xs := fun h => hab (Or.inl h)
              have hb : some b ∉ xs := fun h => hab (Or.inr (Or.inl h))
              have he : a ≠ b := fun h => hab (Or.inr (Or.inr h))
              rw [hfull (some a) (some b) (by simpa [List.nodup_cons, ha, hb, he] using hnd)]
              simp [squarefreeResidualHessian, ha, hb, he]
              ring
      unfold constantHessianForm
      have hmatrix : (fun i j =>
          ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j
            (xs.foldr (fun s f => MvPolynomial.pderiv s f)
              (∑ A : Finset α, MvPolynomial.C (w A) *
                MvPolynomial.X none ^ (Fintype.card α - A.card) *
                  ∏ a ∈ A, MvPolynomial.X (some a))))) : ℚ) : ℝ)) =
          (Nat.factorial (xs.count none) : ℝ) •
            squarefreeResidualHessian w (xs.filterMap id).toFinset (xs.count none) := by
        ext i j
        exact hentry i j
      rw [hmatrix]
      simp only [Matrix.toQuadraticForm', map_smul,
        LinearMap.BilinMap.toQuadraticMap_smul]
      rfl
  · refine ⟨∅, Fintype.card α - 2, 0, le_rfl, ?_, ?_⟩
    · simp only [Finset.card_empty]
      omega
    · rw [zero_smul]
      have hpzero := squarefree_fold_zero_of_not_nodup w xs hnd
      rw [hpzero]
      ext v
      simp only [constantHessianForm, map_zero, Rat.cast_zero,
        Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
        QuadraticMap.zero_apply]
      change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v = 0
      rw [map_zero]
      rfl

end CountingMatroid.Analysis.SquarefreeCoordinateHessian

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed the coordinate Hessian identity using the full-derivative coefficient formula; all four entries have the common homogenizer factorial, and repeated labels give zero.

* 2026-10-09 · partial · after live handoff deferral, proved coordinate-fold commutation and monomial annihilation when a derivative count exceeds its exponent. This closes the normal form for repeated labels anywhere in the list. Only the distinct-label factorial coefficient identity remains open.
* 2026-10-09 · decomposed · defined the exact residual Hessian and proved the derivative-list cardinality identity; instantiated the distinct-label witnesses and reduced the normal form to monomial coefficient extraction. Repeated-label annihilation remains part of the same polynomial obligation.
-/
