import CountingMatroid.Analysis.OmittedTutteNormalization
set_option autoImplicit false

/-! Exact selected-state sums for arbitrary assignments. Tutte normalization,
assigned-label derivatives and pair identification yield the operational
rank weights. The occupancy-to-classification conversion is separate. -/
namespace CountingMatroid.Analysis.ConditionalSelectedStateSum

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators
open Classical

/-- INTERNAL: Delete only the homogenizing variable before conditioning.
TEXLINE: main.tex:354-367,403-417 -/
noncomputable def project {n : ℕ} (g : MvPolynomial (Option (PairedGround n)) ℚ) :
    MvPolynomial (PairedGround n) ℚ :=
  linearSubstitution (fun s t => if s = some t then 1 else 0) g

/-- INTERNAL: Condition an already normalized polynomial on paired labels.
TEXLINE: main.tex:354-367,403-417 -/
noncomputable def conditionSelected {n : ℕ} (σ : Assignment n) (g : MvPolynomial (PairedGround n) ℚ) :
    MvPolynomial (Fin n) ℚ :=
  linearSubstitution (fun e t => if σ e.1 = none ∧ e.1 = t then 1 else 0)
    ((assignedPairs σ).toList.foldl
      (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) g)

/-- INTERNAL: Move the proved Tutte normalization through assigned-label derivatives and pair substitution.
TEXLINE: main.tex:354-367,403-417 -/
theorem conditioned_selected_sum {n : ℕ} (M₁ M₂ : Matroid (Fin n)) (q : ℚ) (σ : Assignment n) :
    conditionedPairPolynomial M₁ M₂ q σ =
      conditionSelected σ (∑ A : PairedSet n, if A.card = n then
        MvPolynomial.monomial (labelExponent A)
          (q ^ n * (q ^ ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat)⁻¹)
        else 0) := by
  classical
  have hproj (g : MvPolynomial (Option (PairedGround n)) ℚ) (e : PairedGround n) :
      project (MvPolynomial.pderiv (some e) g) = MvPolynomial.pderiv e (project g) := by
    ext d
    simp only [project, restriction_coefficient _ (Option.some_injective _), MvPolynomial.coeff_pderiv]
    rw [Finsupp.mapDomain_apply (Option.some_injective (PairedGround n))]
    congr 2
    rw [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
  have hfold (l : List (Fin n)) (g : MvPolynomial (Option (PairedGround n)) ℚ) :
      project (l.foldl (fun p i => MvPolynomial.pderiv (some (i, (σ i).getD false)) p) g) =
        l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (project g) := by
    induction l generalizing g with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons, ih, hproj]
  have hC (l : List (Fin n)) (g : MvPolynomial (PairedGround n) ℚ) (c : ℚ) :
      l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (MvPolynomial.C c * g) =
        MvPolynomial.C c * l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) g := by
    induction l generalizing g with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons, MvPolynomial.pderiv_C_mul, ih]
  have hsub (g : MvPolynomial (Option (PairedGround n)) ℚ) :
      linearSubstitution (conditionedPairSubstitution σ) g =
        linearSubstitution (fun e t => if σ e.1 = none ∧ e.1 = t then 1 else 0) (project g) := by
    unfold project linearSubstitution
    rw [MvPolynomial.comp_aeval_apply]
    congr 1
    congr 1
    funext s
    cases s <;> simp [conditionedPairSubstitution]
  rw [← normalized_tutte_polynomial (pairedMatroid M₁ M₂) q n (by simp [PairedGround, Nat.mul_comm])]
  unfold conditionedPairPolynomial conditionSelected
  rw [hsub, hfold, hC]
  simp [linearSubstitution, project]

/-- INTERNAL: List each prescribed label exactly once.
TEXLINE: main.tex:354-367,403-417 -/
noncomputable def selectedLabelList {n : ℕ} (σ : Assignment n) : List (PairedGround n) :=
  (assignedPairs σ).toList.map (fun i => (i, (σ i).getD false))

/-- INTERNAL: Compute the conditioning operator by exact squarefree selected-label extraction.
TEXLINE: main.tex:354-367,403-417 -/
theorem condition_selected_coefficient {n : ℕ} (σ : Assignment n) (g : MvPolynomial (PairedGround n) ℚ)
    (d : Fin n →₀ ℕ) :
    (conditionSelected σ g).coeff d =
      ∑ u ∈ ((selectedLabelList σ).foldl (fun p e => MvPolynomial.pderiv e p) g).support,
        if (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d then
          g.coeff (u + labelExponent (selectedLabelList σ).toFinset) else 0 := by
  classical
  have hl : (selectedLabelList σ).Nodup :=
    (Finset.nodup_toList _).map (by intro i j h; exact congrArg Prod.fst h)
  unfold conditionSelected
  rw [show (assignedPairs σ).toList.foldl
      (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) g =
      (selectedLabelList σ).foldl (fun p e => MvPolynomial.pderiv e p) g by
        simp [selectedLabelList, List.foldl_map]]
  rw [masked_substitution_coefficient]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases ha : (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d
  · rw [if_pos ha, if_pos ha, derivative_list_coefficient _ hl]
    · congr 2
      exact (List.sum_toFinset (fun e : PairedGround n => (Finsupp.single e 1 : PairedGround n →₀ ℕ)) hl).symm
    · intro e he
      obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
      by_contra hne
      have hz := ha.1 (i, (σ i).getD false) (Finsupp.mem_support_iff.mpr hne)
      exact (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2 hz
  · rw [if_neg ha, if_neg ha]

/-- INTERNAL: A selected-state monomial survives precisely its assignment and pair-occupancy tests.
TEXLINE: main.tex:354-367,403-417 -/
theorem condition_selected_monomial_coefficient {n : ℕ} (σ : Assignment n) (A : PairedSet n) (c : ℚ) (d : Fin n →₀ ℕ) :
    (conditionSelected σ (MvPolynomial.monomial (labelExponent A) c)).coeff d =
      if (selectedLabelList σ).toFinset ⊆ A ∧
        (∀ e ∈ A \ (selectedLabelList σ).toFinset, σ e.1 = none) ∧
        (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d then c else 0 := by
  classical
  rw [condition_selected_coefficient]
  let C := (selectedLabelList σ).toFinset
  let v₀ := labelExponent (A \ C)
  have hl : (selectedLabelList σ).Nodup :=
    (Finset.nodup_toList _).map (by intro i j h; exact congrArg Prod.fst h)
  have hsupport (S : PairedSet n) (e : PairedGround n) :
      e ∈ (labelExponent S).support ↔ e ∈ S := by
    simp [Finsupp.mem_support_iff, label_exponent_apply]
  have hvzero : ∀ e ∈ selectedLabelList σ, v₀ e = 0 := by
    intro e he
    simp [v₀, label_exponent_apply, C, List.mem_toFinset.mpr he]
  change (∑ v ∈ ((selectedLabelList σ).foldl (fun p e => MvPolynomial.pderiv e p)
      (MvPolynomial.monomial (labelExponent A) c)).support,
      if (∀ e ∈ v.support, σ e.1 = none) ∧ v.mapDomain Prod.fst = d then
        (MvPolynomial.monomial (labelExponent A) c).coeff (v + labelExponent C) else 0) =
    if C ⊆ A ∧ (∀ e ∈ A \ C, σ e.1 = none) ∧ v₀.mapDomain Prod.fst = d then c else 0
  by_cases hCA : C ⊆ A
  · have hexp : v₀ + labelExponent C = labelExponent A := by
      ext e
      simp only [Finsupp.add_apply, v₀, label_exponent_apply, Finset.mem_sdiff]
      by_cases heC : e ∈ C
      · have heA := hCA heC
        simp [heC, heA]
      · by_cases heA : e ∈ A <;> simp [heC, heA]
    have heq' (v : PairedGround n →₀ ℕ) : labelExponent A = v + labelExponent C ↔ v = v₀ := by
      rw [← hexp]
      exact eq_comm.trans add_right_cancel_iff
    simp_rw [MvPolynomial.coeff_monomial, heq']
    rw [Finset.sum_eq_single v₀]
    · simp only [ite_and, if_pos hCA, v₀, hsupport, ite_true]
    · intro v hv hne
      simp [hne]
    · intro hnot
      have hd := MvPolynomial.notMem_support_iff.mp hnot
      rw [derivative_list_coefficient _ hl _ v₀ hvzero] at hd
      have hsum : ((selectedLabelList σ).map (fun e => Finsupp.single e 1)).sum = labelExponent C :=
        (List.sum_toFinset (fun e : PairedGround n => (Finsupp.single e 1 : PairedGround n →₀ ℕ)) hl).symm
      rw [hsum, hexp, MvPolynomial.coeff_monomial, if_pos rfl] at hd
      simp [hd]
  · have hfalse (v : PairedGround n →₀ ℕ) : v + labelExponent C ≠ labelExponent A := by
      intro hv
      apply hCA
      intro e heC
      have he := DFunLike.congr_fun hv e
      rw [Finsupp.add_apply, label_exponent_apply C, if_pos heC,
        label_exponent_apply A] at he
      by_contra hn
      rw [if_neg hn] at he
      omega
    simp only [MvPolynomial.coeff_monomial]
    simp_rw [if_neg (hfalse _).symm]
    simp only [ite_self, Finset.sum_const_zero]
    rw [if_neg (by rintro ⟨h, _⟩; exact hCA h)]

/-- INTERNAL: The derivative list records exactly the prescribed label at each assigned pair.
TEXLINE: main.tex:354-367,403-417 -/
theorem selected_label_mem {n : ℕ} (σ : Assignment n) (i : Fin n) (b : Bool) :
    (i, b) ∈ (selectedLabelList σ).toFinset ↔ σ i = some b := by
  classical
  cases h : σ i <;> simp [selectedLabelList, assignedPairs, h]

/-- INTERNAL: The polynomial extraction and deletion tests are the operational assignment predicate.
TEXLINE: main.tex:354-367,403-417 -/
theorem selected_labels_respects {n : ℕ} (σ : Assignment n) (A : PairedSet n) :
    (selectedLabelList σ).toFinset ⊆ A ∧ (∀ e ∈ A \ (selectedLabelList σ).toFinset, σ e.1 = none) ↔
      Respects σ A := by
  classical
  constructor
  · rintro ⟨hsub, ha⟩ i b hb
    refine ⟨hsub ((selected_label_mem σ i b).mpr hb), ?_⟩
    intro hm
    have hnot : (i, !b) ∉ (selectedLabelList σ).toFinset := by
      rw [selected_label_mem, hb]
      cases b <;> simp
    have hz := ha (i, !b) (Finset.mem_sdiff.mpr ⟨hm, hnot⟩)
    rw [hb] at hz
    cases hz
  · intro h
    constructor
    · rintro ⟨i, b⟩ he
      exact (h i b ((selected_label_mem σ i b).mp he)).1
    · rintro ⟨i, b⟩ he
      obtain ⟨heA, hen⟩ := Finset.mem_sdiff.mp he
      cases hi : σ i with
      | none => rfl
      | some c =>
        have hc := h i c hi
        have hbc : b = c := by
          cases b <;> cases c <;> simp_all
        subst c
        exact False.elim (hen ((selected_label_mem σ i b).mpr hi))

/-- INTERNAL: Identify every conditioned coefficient with a finite operational rank-weight state sum.
TEXLINE: main.tex:354-367,403-417 -/
theorem conditioned_state_coefficient {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) (hq : 0 < q)
    (σ : Assignment n) (d : Fin n →₀ ℕ) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff d =
      ∑ A : PairedSet n, if A.card = n ∧ Respects σ A ∧
          (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ A).val) else 0 := by
  classical
  rw [conditioned_selected_sum]
  have hadd (l : List (Fin n)) (f : PairedSet n → MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (∑ A, f A) =
        ∑ A, l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p) (f A) := by
    induction l generalizing f with
    | nil => rfl
    | cons i l ih => simp only [List.foldl_cons, map_sum, ih]
  unfold conditionSelected
  rw [hadd]
  simp only [linearSubstitution, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro A _
  by_cases hc : A.card = n
  · rw [if_pos hc]
    change (conditionSelected σ (MvPolynomial.monomial (labelExponent A) _)).coeff d = _
    rw [condition_selected_monomial_coefficient]
    have hpat : ((selectedLabelList σ).toFinset ⊆ A ∧
        (∀ e ∈ A \ (selectedLabelList σ).toFinset, σ e.1 = none) ∧
          (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d) ↔
        Respects σ A ∧ (labelExponent (A \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst = d := by
      rw [← and_assoc, selected_labels_respects]
    simp only [hpat]
    simp only [hc, true_and]
    split_ifs
    · rw [CountingMatroid.Analysis.PairedRankValue.paired_rank_eq_eRk r M₁ M₂ o₁ o₂ hfull hr h₁ h₂]
      have hle : ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat ≤ n := by
        apply ENat.toNat_le_of_le_natCast
        simpa only [Set.encard_coe_eq_coe_finsetCard, hc] using
          (pairedMatroid M₁ M₂).eRk_le_encard (A : Set (PairedGround n))
      rw [show q ^ n = q ^ (n - ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat) *
        q ^ ((pairedMatroid M₁ M₂).eRk (A : Set (PairedGround n))).toNat by
          rw [← pow_add, Nat.sub_add_cancel hle]]
      field_simp [pow_ne_zero _ hq.ne']
    · rfl
  · rw [if_neg hc, if_neg (by rintro ⟨h, _⟩; exact hc h)]
    have hz (l : List (Fin n)) :
        l.foldl (fun p i => MvPolynomial.pderiv (i, (σ i).getD false) p)
          (0 : MvPolynomial (PairedGround n) ℚ) = 0 := by
      induction l with
      | nil => rfl
      | cons i l ih => simp only [List.foldl_cons, map_zero, ih]
    simp [hz]

/-- INTERNAL: Pair identification sums the two squarefree label exponents.
TEXLINE: main.tex:354-367,403-417 -/
theorem occupancy_apply {n : ℕ} (S : PairedSet n) (i : Fin n) :
    (labelExponent S).mapDomain Prod.fst i =
      (if (i, false) ∈ S then 1 else 0) + (if (i, true) ∈ S then 1 else 0) := by
  classical
  rw [labelExponent, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  calc
    (∑ e ∈ S, if e.1 = i then 1 else 0) =
        ∑ e : PairedGround n, if e ∈ S ∧ e.1 = i then 1 else 0 := by
      simp only [ite_and]
      rw [Finset.sum_ite_mem]
      simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      simp [ite_and, Finset.sum_ite, eq_comm]
      by_cases hx : (i, false) ∈ S <;> by_cases hy : (i, true) ∈ S <;> simp [Finset.filter_insert, Finset.filter_singleton, hx, hy]

/-- INTERNAL: Ordinary-pair extraction contributes one precisely at unassigned nonretained pairs.
TEXLINE: main.tex:354-367,403-417 -/
theorem ordinary_exponent_apply {n : ℕ} (σ : Assignment n) (T : Finset (Fin n)) (i : Fin n) :
    ordinaryExponent σ T i = if σ i = none ∧ i ∉ T then 1 else 0 := by
  classical
  simp [ordinaryExponent, ← List.sum_toFinset _ (Finset.nodup_toList _),
    Finsupp.single_apply, assignedPairs, eq_comm]

/-- INTERNAL: At respecting states the surviving exponent counts only unassigned labels.
TEXLINE: main.tex:354-367,403-417 -/
theorem respects_occupancy_apply {n : ℕ} (σ : Assignment n) (S : PairedSet n)
    (hS : Respects σ S) (i : Fin n) :
    (labelExponent (S \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst i =
      if σ i = none then
        (if (i, false) ∈ S then 1 else 0) + (if (i, true) ∈ S then 1 else 0) else 0 := by
  rw [occupancy_apply]
  simp only [Finset.mem_sdiff, selected_label_mem]
  cases hi : σ i with
  | none => simp
  | some b =>
    have h := hS i b hi
    cases b <;> simp_all

end CountingMatroid.Analysis.ConditionalSelectedStateSum

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · exact normalization through assigned-label conditioning, monomial survival, operational assignment equivalence and finite paired-state coefficient sums; also proved the pair-occupancy and ordinary-exponent evaluations used by the coefficient classifier.
-/
