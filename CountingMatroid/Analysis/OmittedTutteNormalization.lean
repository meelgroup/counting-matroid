import CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
import CountingMatroid.Analysis.PairedRankValue
import CountingMatroid.Analysis.OmittedRankWeightPolynomial
import CountingMatroid.Analysis.OmittedSlotQuadratic

set_option autoImplicit false

/-! Exact normalization and rank correspondence for the omitted-label Tutte
slice and its slot extraction. These identities do not assume coefficient
identification for the final transport Hessian. -/
namespace CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators

/-- INTERNAL: Squarefree selected-label exponent vector used to expand Tutte terms.
TEXLINE: main.tex:334-339 -/
noncomputable def labelExponent {α : Type} (A : Finset α) : α →₀ ℕ :=
  ∑ e ∈ A, Finsupp.single e 1

/-- INTERNAL: Evaluate a squarefree selected-label exponent. -/
lemma label_exponent_apply {α : Type} [DecidableEq α] (A : Finset α) (e : α) :
    labelExponent A e = if e ∈ A then 1 else 0 := by
  classical
  simp [labelExponent, Finsupp.single_apply, eq_comm]

/-- INTERNAL: Express one homogenized Tutte summand as one monomial.
TEXLINE: main.tex:334-339 -/
lemma tutte_term_monomial {α : Type} [Fintype α] (N : Matroid α) (q : ℚ) (A : Finset α) :
    MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
      MvPolynomial.X none ^ (Fintype.card α - A.card) *
        ∏ e ∈ A, MvPolynomial.X (some e) =
    MvPolynomial.monomial
      ((labelExponent A).mapDomain Option.some + Finsupp.single none (Fintype.card α - A.card))
      ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) := by
  classical
  have hprod : (∏ e ∈ A, MvPolynomial.X (some e) : MvPolynomial (Option α) ℚ) =
      MvPolynomial.monomial ((labelExponent A).mapDomain Option.some) 1 := by
    unfold labelExponent
    rw [Finsupp.mapDomain_finsetSum]
    simp only [Finsupp.mapDomain_single]
    simpa [MvPolynomial.X] using (MvPolynomial.monomial_sum_prod A
      (fun e => Finsupp.single (some e) 1) (fun _ => (1 : ℚ))).symm
  rw [hprod, MvPolynomial.X_pow_eq_monomial, MvPolynomial.C_mul_monomial,
    MvPolynomial.monomial_mul, mul_one, mul_one]
  congr 1
  ac_rfl

/-- INTERNAL: Normalized homogenizer extraction retains exactly the half-ground subsets,
with the derivative multiplicity cancelled.
TEXLINE: main.tex:354-367 -/
lemma normalized_tutte_coefficient {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (m : ℕ) (hcard : Fintype.card α = 2 * m)
    (d : α →₀ ℕ) :
    (MvPolynomial.C (q ^ m / (m.factorial : ℚ)) *
      linearSubstitution (fun s t => if s = some t then 1 else 0)
        ((MvPolynomial.pderiv none)^[m] (tuttePolynomial N q))).coeff d =
      ∑ A : Finset α, if A.card = m ∧ labelExponent A = d then
        q ^ m * (q ^ (N.eRk (A : Set α)).toNat)⁻¹ else 0 := by
  classical
  rw [MvPolynomial.coeff_C_mul, restriction_coefficient _ (Option.some_injective α),
    homogenizer_derivative_coefficient _ _ _
      (Finsupp.mapDomain_of_notMem_range _ _ (by rintro ⟨e, he⟩; cases he))]
  have hf : (m.factorial : ℚ) ≠ 0 := by positivity
  have hcancel : q ^ m / (m.factorial : ℚ) *
      ((tuttePolynomial N q).coeff (d.mapDomain Option.some + Finsupp.single none m) *
        (m.factorial : ℚ)) =
      q ^ m * (tuttePolynomial N q).coeff (d.mapDomain Option.some + Finsupp.single none m) := by
    field_simp
  rw [hcancel, tuttePolynomial, MvPolynomial.coeff_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  rw [tutte_term_monomial, MvPolynomial.coeff_monomial]
  have heq :
      (labelExponent A).mapDomain Option.some + Finsupp.single none (Fintype.card α - A.card) =
        d.mapDomain Option.some + Finsupp.single none m ↔ A.card = m ∧ labelExponent A = d := by
    constructor
    · intro h
      have hz (v : α →₀ ℕ) : (v.mapDomain Option.some) none = 0 :=
        Finsupp.mapDomain_of_notMem_range v none (by rintro ⟨e, he⟩; cases he)
      have hn := DFunLike.congr_fun h none
      simp only [Finsupp.add_apply, Finsupp.single_eq_same, hz, zero_add] at hn
      have hle := Finset.card_le_univ A
      have ha : A.card = m := by omega
      refine ⟨ha, ?_⟩
      ext e
      have hs := DFunLike.congr_fun h (some e)
      simpa [Finsupp.mapDomain_apply (Option.some_injective α), Finsupp.single_apply] using hs
    · rintro ⟨ha, rfl⟩
      rw [ha, hcard, show 2 * m - m = m by omega]
  simp only [heq]
  split_ifs <;> simp

/-- PAPER: main.tex:360-364
The normalized homogenizer derivative gives the half-ground rank-weight polynomial. -/
lemma normalized_tutte_polynomial {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (m : ℕ) (hcard : Fintype.card α = 2 * m) :
    MvPolynomial.C (q ^ m / (m.factorial : ℚ)) *
      linearSubstitution (fun s t => if s = some t then 1 else 0)
        ((MvPolynomial.pderiv none)^[m] (tuttePolynomial N q)) =
      ∑ A : Finset α, if A.card = m then
        MvPolynomial.monomial (labelExponent A)
          (q ^ m * (q ^ (N.eRk (A : Set α)).toNat)⁻¹) else 0 := by
  classical
  ext d
  rw [normalized_tutte_coefficient N q m hcard, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hc : A.card = m <;> simp [hc, MvPolynomial.coeff_monomial]

/-- PAPER: main.tex:262-272
The paired matroid has rank n under the two common-rank promises. -/
lemma paired_matroid_eRank {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂) :
    (pairedMatroid M₁ M₂).eRank = n := by
  have hdual := M₂.eRank_add_eRank_dual
  simp only [hr.2, hfull.2, Set.encard_univ, ENat.card_eq_coe_fintype_card, Fintype.card_fin] at hdual
  have htotal := PairedRankValue.paired_matroid_eRk M₁ M₂ hfull Set.univ
  simp only [Set.mem_univ, Set.setOf_true, Matroid.eRk_univ_eq, hr.1] at htotal
  exact htotal.trans hdual

/-- PAPER: main.tex:365-367
On half-ground sets, dual rank equals the operational paired rank of the complement. -/
lemma dual_paired_rank {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (state : PairedSet n) (hcard : state.card = n) :
    (((pairedMatroid M₁ M₂)✶).eRk ((Finset.univ \ state : PairedSet n) : Set (PairedGround n))).toNat =
      (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val := by
  classical
  let K := pairedMatroid M₁ M₂
  have hK : K.E = Set.univ := paired_matroid_full_ground M₁ M₂ hfull
  have hrank : K.eRank = n := paired_matroid_eRank r M₁ M₂ hfull hr
  have hc : (Finset.univ \ state : PairedSet n).card = n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, hcard]
    simp only [PairedGround, Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    omega
  have hcompl : K.E \ ((Finset.univ \ state : PairedSet n) : Set (PairedGround n)) = state := by
    rw [hK]
    ext e
    simp
  have hd := K.eRk_dual_add_eRank
    ((Finset.univ \ state : PairedSet n) : Set (PairedGround n))
    (by rw [hK]; exact Set.subset_univ _)
  rw [hrank, hcompl, Set.encard_coe_eq_coe_finsetCard, hc] at hd
  have hfinite (N : Matroid (PairedGround n)) (S : Set (PairedGround n)) : N.eRk S ≠ ⊤ :=
    (N.isRkFinite_of_finite (Set.toFinite S)).eRk_lt_top.ne
  have hd' := congrArg ENat.toNat hd
  simp only [ENat.toNat_add (hfinite _ _) (ENat.coe_ne_top n), ENat.toNat_natCast] at hd'
  rw [PairedRankValue.paired_rank_eq_eRk r M₁ M₂ o₁ o₂ hfull hr h₁ h₂ state]
  exact Nat.add_right_cancel hd'


/-- PAPER: main.tex:354-367
The normalized dual Tutte slice is exactly the operational omitted-label polynomial. -/
lemma normalized_omitted_polynomial {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hq : 0 < q) :
    MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
      linearSubstitution OmittedSlotQuadratic.omitHomogenizer
        ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂)✶ q)) =
      OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q := by
  classical
  have hsub : OmittedSlotQuadratic.omitHomogenizer (n := n) =
      fun s t => if s = some t then 1 else 0 := by
    funext s t
    cases s <;> simp [OmittedSlotQuadratic.omitHomogenizer]
  rw [hsub, normalized_tutte_polynomial _ q n (by simp [PairedGround, Nat.mul_comm])]
  unfold OmittedRankWeightPolynomial.omittedRankPolynomial
  apply Fintype.sum_bijective (fun A : PairedSet n => Finset.univ \ A)
    (show Function.Bijective (fun A : PairedSet n => Finset.univ \ A) from
      (show Function.Involutive (fun A : PairedSet n => Finset.univ \ A) from by
        intro A; ext e; simp).bijective)
  intro A
  have hc : (Finset.univ \ A : PairedSet n).card = n ↔ A.card = n := by
    rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ]
    have hle := Finset.card_le_univ A
    simp only [PairedGround, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] at *
    omega
  by_cases ha : A.card = n
  · rw [if_pos ha, if_pos (hc.mpr ha)]
    have he : labelExponent A =
        OmittedRankWeightPolynomial.omittedExponent (Finset.univ \ A : PairedSet n) := by
      ext e
      rw [label_exponent_apply, OmittedRankWeightPolynomial.omitted_exponent_apply]
      simp
    rw [he]
    congr 1
    have hcompl : (Finset.univ \ (Finset.univ \ A) : PairedSet n) = A := by ext e; simp
    have hrk := dual_paired_rank r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
      (Finset.univ \ A) (hc.mpr ha)
    rw [hcompl] at hrk
    rw [hrk]
    have hle : (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val ≤ n := by
      rw [← hrk]
      apply ENat.toNat_le_of_le_natCast
      simpa only [Set.encard_coe_eq_coe_finsetCard, ha] using
        ((pairedMatroid M₁ M₂)✶).eRk_le_encard (A : Set (PairedGround n))
    have hpow : q ^ n = q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val) *
        q ^ (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val := by
      rw [← pow_add, Nat.sub_add_cancel hle]
    rw [hpow]
    have hne : q ^ (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ (Finset.univ \ A)).val ≠ 0 :=
      pow_ne_zero _ hq.ne'
    field_simp
  · rw [if_neg ha, if_neg (by simpa only [hc] using ha)]

/-- INTERNAL: Apply the existing omitted-slot extraction to the operational polynomial.
TEXLINE: main.tex:584-601 -/
noncomputable def operationalSlotQuadratic {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n) :
    MvPolynomial (R ⊕ Bool) ℚ :=
  let G := linearSubstitution (OmittedSlotQuadratic.slotSubstitution R U t)
    (OmittedSlotQuadratic.differentiateLabels (OmittedSlotQuadratic.fixedOmissions B R U)
      (OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q))
  let H := (U.erase t).toList.foldl (fun p s => OmittedSlotQuadratic.extractLabel (s, false) p) G
  linearSubstitution (OmittedSlotQuadratic.activeSubstitution R t) H

/-- INTERNAL: Transfer the exact normalized rank-weight identity through all slot-extraction operations.
TEXLINE: main.tex:584-601 -/
lemma normalized_omitted_slot {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hq : 0 < q)
    (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n) :
    OmittedSlotQuadratic.omittedSlotQuadratic (pairedMatroid M₁ M₂)✶ q B R U t =
      operationalSlotQuadratic r o₁ o₂ q B R U t := by
  classical
  have hsub {α β : Type} [Fintype β] (a : α → β → ℚ) (c : ℚ) (g : MvPolynomial α ℚ) :
      linearSubstitution a (MvPolynomial.C c * g) =
        MvPolynomial.C c * linearSubstitution a g := by
    simp [linearSubstitution]
  have hdiff (l : List (PairedGround n)) (c : ℚ) (g : MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p e => MvPolynomial.pderiv e p) (MvPolynomial.C c * g) =
        MvPolynomial.C c * l.foldl (fun p e => MvPolynomial.pderiv e p) g := by
    induction l generalizing g with
    | nil => rfl
    | cons e l ih => simp only [List.foldl_cons, MvPolynomial.pderiv_C_mul, ih]
  have hextract (l : List (Fin n)) (c : ℚ) (g : MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p s => OmittedSlotQuadratic.extractLabel (s, false) p) (MvPolynomial.C c * g) =
        MvPolynomial.C c * l.foldl (fun p s => OmittedSlotQuadratic.extractLabel (s, false) p) g := by
    induction l generalizing g with
    | nil => rfl
    | cons e l ih =>
      simp only [List.foldl_cons]
      have hstep : OmittedSlotQuadratic.extractLabel (e, false) (MvPolynomial.C c * g) =
          MvPolynomial.C c * OmittedSlotQuadratic.extractLabel (e, false) g := by
        unfold OmittedSlotQuadratic.extractLabel
        rw [MvPolynomial.pderiv_C_mul, hsub]
      rw [hstep, ih]
  unfold operationalSlotQuadratic OmittedSlotQuadratic.omittedSlotQuadratic
  rw [← normalized_omitted_polynomial r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq]
  simp only [OmittedSlotQuadratic.differentiateLabels, hdiff, hsub, hextract]
end CountingMatroid.Analysis.OmittedTutteNormalization
