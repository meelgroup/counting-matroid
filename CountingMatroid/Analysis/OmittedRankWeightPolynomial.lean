import CountingMatroid.Analysis.ConditionalDefectCoefficients
import Mathlib.Algebra.MvPolynomial.Degrees
import Mathlib.Data.Finsupp.Indicator

set_option autoImplicit false

/-!
The omitted-element rank-weight polynomial, expressed using the operational
paired-rank scan. Its coefficients below are identified with the operational
conditional defect totals. These identities do not assert a Hessian signature
or identify this scan with the rank of a matroid.
-/

namespace CountingMatroid.Analysis.OmittedRankWeightPolynomial

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open scoped BigOperators
open Classical

/-- INTERNAL: Squarefree exponent vector of the labels omitted by a state.
TEXLINE: main.tex:571-625 -/
noncomputable def omittedExponent {n : ℕ} (state : PairedSet n) :
    PairedGround n →₀ ℕ :=
  Finsupp.indicator (Finset.univ \ state) (fun _ _ => 1)

/-- INTERNAL: Each omitted label occurs once, and every selected label has
exponent zero.
TEXLINE: main.tex:571-625 -/
theorem omitted_exponent_apply {n : ℕ} (state : PairedSet n) (e : PairedGround n) :
    omittedExponent state e = if e ∈ state then 0 else 1 := by
  classical
  simp [omittedExponent]

/-- INTERNAL: Omitted-label exponent vectors recover the entire paired state.
TEXLINE: main.tex:571-625 -/
theorem omitted_exponent_injective {n : ℕ} :
    Function.Injective (@omittedExponent n) := by
  classical
  intro state next h
  ext e
  have he := DFunLike.congr_fun h e
  rw [omitted_exponent_apply, omitted_exponent_apply] at he
  by_cases hs : e ∈ state <;> by_cases ht : e ∈ next <;> simp_all

/-- INTERNAL: Operational version of the homogeneous omitted-element
rank-weight polynomial, before the paired-rank/matroid-rank bridge.
TEXLINE: main.tex:571-625 -/
noncomputable def omittedRankPolynomial {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) : MvPolynomial (PairedGround n) ℚ := by
  classical
  exact ∑ state : PairedSet n, if state.card = n then
    MvPolynomial.monomial (omittedExponent state)
      (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val))
    else 0

/-- INTERNAL: The squarefree coefficient indexed by a state's omitted
labels is its exact operational rank weight, guarded only by cardinality.
TEXLINE: main.tex:571-625 -/
theorem omitted_rank_coefficient {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (state : PairedSet n) :
    MvPolynomial.coeff (omittedExponent state) (omittedRankPolynomial r o₁ o₂ q) =
      if state.card = n then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
      else 0 := by
  classical
  unfold omittedRankPolynomial
  rw [MvPolynomial.coeff_sum]
  have hterm (next : PairedSet n) :
      MvPolynomial.coeff (omittedExponent state)
        (if next.card = n then MvPolynomial.monomial (omittedExponent next)
          (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ next).val))
        else 0) =
      if next = state then
        (if next.card = n then
          q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ next).val)
        else 0) else 0 := by
    have heq : omittedExponent next = omittedExponent state ↔ next = state :=
      omitted_exponent_injective.eq_iff
    by_cases hc : next.card = n <;> simp [hc, MvPolynomial.coeff_monomial, heq]
  simp_rw [hterm]
  simp

/-- INTERNAL: A completed ordered defect occupies exactly n labels.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_completion_card {n : ℕ} (σ : Assignment n) (index : DefectIndex n) :
    (defectCompletion σ index).card = n := by
  classical
  have hdisjoint : Disjoint
      (((Finset.univ.erase index.emptyPair).erase index.fullPair).image
        (fun i => (i, (σ i).getD false)))
      ({(index.fullPair, false), (index.fullPair, true)} : PairedSet n) := by
    rw [Finset.disjoint_left]
    intro e he hf
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp he
    have hin : i ≠ index.fullPair := (Finset.mem_erase.mp hi).1
    simp [hin] at hf
  unfold defectCompletion
  rw [Finset.card_union_of_disjoint hdisjoint, Finset.card_image_of_injective]
  · rw [Finset.card_erase_of_mem (by simp [index.distinct.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ _)]
    simp
    have hi := index.emptyPair.isLt
    have hk := index.fullPair.isLt
    have hne : index.emptyPair.val ≠ index.fullPair.val :=
      fun h => index.distinct (Fin.ext h)
    omega
  · intro i j h
    exact congrArg Prod.fst h

/-- INTERNAL: Recover an accepted defect as a completion of its ordinary
pair choices, using the executable classifier's proved occupancy description.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_is_completion {n : ℕ} (state : PairedSet n) (index : DefectIndex n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    defectCompletion (fun i => some (decide ((i, true) ∈ state))) index = state := by
  classical
  obtain ⟨he, hf⟩ := (InitialMultipliersGood.classify_defect_iff state index).mp hkind
  ext ⟨i, b⟩
  rw [mem_defect_completion]
  have hei := he i
  have hfi := hf i
  cases b <;> by_cases hx : (i, false) ∈ state <;>
    by_cases hy : (i, true) ∈ state <;> simp_all [index.distinct]

/-- INTERNAL: Every accepted defect has the cardinality guard required by
the omitted-element polynomial.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_card {n : ℕ} (state : PairedSet n) (index : DefectIndex n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    state.card = n := by
  rw [← defect_is_completion state index hkind]
  exact defect_completion_card _ _

/-- INTERNAL: The conditional defect coefficient is exactly the sum of
coefficients of the omitted-element polynomial on the matching states.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_coefficient_sum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (index : DefectIndex n) :
    (∑ state : PairedSet n,
      if Respects σ state ∧
          (classifyState state).val = .defect index.emptyPair index.fullPair then
        MvPolynomial.coeff (omittedExponent state) (omittedRankPolynomial r o₁ o₂ q)
      else 0) = defectTotal r o₁ o₂ q σ index := by
  classical
  unfold defectTotal
  apply Finset.sum_congr rfl
  intro state _
  by_cases h : Respects σ state ∧
      (classifyState state).val = .defect index.emptyPair index.fullPair
  · rw [if_pos h, if_pos h, omitted_rank_coefficient, if_pos (defect_card _ _ h.2)]
  · rw [if_neg h, if_neg h]

/-- INTERNAL: Positivity of the polynomial's conditional defect coefficient
sum follows from an actual defect completion and nonnegative coefficients.
TEXLINE: main.tex:383-392,571-625 -/
theorem defect_coefficient_total_pos {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q)
    (σ : Assignment n) (index : DefectIndex n)
    (he : σ index.emptyPair = none) (hf : σ index.fullPair = none) :
    0 < (∑ state : PairedSet n,
      if Respects σ state ∧
          (classifyState state).val = .defect index.emptyPair index.fullPair then
        MvPolynomial.coeff (omittedExponent state) (omittedRankPolynomial r o₁ o₂ q)
      else 0) := by
  classical
  let term := fun state : PairedSet n =>
    if Respects σ state ∧
        (classifyState state).val = .defect index.emptyPair index.fullPair then
      MvPolynomial.coeff (omittedExponent state) (omittedRankPolynomial r o₁ o₂ q)
    else 0
  have hnonneg (state : PairedSet n) : 0 ≤ term state := by
    dsimp only [term]
    split_ifs
    · rw [omitted_rank_coefficient]
      split_ifs
      · exact (pow_pos hq _).le
      · exact le_rfl
    · exact le_rfl
  let S := defectCompletion σ index
  have hS : Respects σ S ∧ (classifyState S).val =
      .defect index.emptyPair index.fullPair :=
    ⟨defect_completion_respects σ index he hf, defect_completion_classified σ index⟩
  have hterm : 0 < term S := by
    dsimp only [term]
    rw [if_pos hS, omitted_rank_coefficient, if_pos (defect_completion_card σ index)]
    exact pow_pos hq _
  exact hterm.trans_le (Finset.single_le_sum (fun state _ => hnonneg state)
    (Finset.mem_univ S))

/-- INTERNAL: The operational omitted-element polynomial is multiaffine;
this gives zero diagonal Hessian entries in active, unmerged variables.
TEXLINE: main.tex:592-593 -/
theorem omitted_rank_multiaffine {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (e : PairedGround n) :
    (omittedRankPolynomial r o₁ o₂ q).degreeOf e ≤ 1 := by
  classical
  apply MvPolynomial.degreeOf_le_iff.mpr
  intro d hd
  unfold omittedRankPolynomial at hd
  obtain ⟨state, _, hs⟩ := Finset.mem_biUnion.mp (MvPolynomial.support_sum hd)
  by_cases hc : state.card = n
  · rw [if_pos hc] at hs
    have heq := MvPolynomial.support_monomial_subset hs
    rw [Finset.mem_singleton] at heq
    rw [heq, omitted_exponent_apply]
    split_ifs <;> omega
  · rw [if_neg hc] at hs
    simpa using hs

end CountingMatroid.Analysis.OmittedRankWeightPolynomial
