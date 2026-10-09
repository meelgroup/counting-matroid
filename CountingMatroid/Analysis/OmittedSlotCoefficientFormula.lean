import CountingMatroid.Analysis.OmittedTutteNormalization

set_option autoImplicit false

/-! Exact coefficient extraction for the omitted-slot quadratic. The final
state sum retains the full omitted-label pattern condition; identifying those
patterns with the transport completion predicates is a separate combinatorial
obligation. No signature inequality is asserted here. -/
namespace CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.OmittedSlotQuadratic
open CountingMatroid.Analysis.OmittedTutteNormalization
open scoped BigOperators
open Classical

/-- INTERNAL: Generalize exponent-one extraction to paired-label variables using the public masked-substitution calculus.
TEXLINE: main.tex:369-373 -/
lemma extract_label_coefficient {n : ℕ} (e : PairedGround n)
    (g : MvPolynomial (PairedGround n) ℚ) (d : PairedGround n →₀ ℕ) (hd : d e = 0) :
    (extractLabel e g).coeff d = g.coeff (d + Finsupp.single e 1) := by
  classical
  have hsub : (fun s f : PairedGround n => if s = e then (0 : ℚ) else if s = f then 1 else 0) =
      fun s f => if s ≠ e ∧ id s = f then 1 else 0 := by
    funext s f
    by_cases hs : s = e <;> simp [hs]
  unfold extractLabel
  rw [hsub, masked_substitution_coefficient]
  simp only [Finsupp.mapDomain_id]
  rw [Finset.sum_eq_single d]
  · rw [if_pos]
    · rw [MvPolynomial.coeff_pderiv]
      simp [hd]
    · refine ⟨?_, rfl⟩
      intro s hs hse
      subst s
      exact Finsupp.mem_support_iff.mp hs hd
  · intro b hb hbd
    simp [hbd]
  · intro hdnot
    have hzero := MvPolynomial.notMem_support_iff.mp hdnot
    rw [hzero]
    simp

/-- INTERNAL: A sum of single exponents vanishes off its variable list. -/
lemma single_list_sum_zero {α : Type} [DecidableEq α] (l : List α)
    (j : α) (hj : j ∉ l) :
    ((l.map (fun i => (Finsupp.single i 1 : α →₀ ℕ))).sum) j = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.mem_cons, not_or] at hj
    simp [hj.1, ih hj.2]

/-- INTERNAL: Distinct paired-label extractions shift the requested coefficient by one in each extracted variable.
TEXLINE: main.tex:587-589 -/
lemma extract_labels_coefficient {n : ℕ} (l : List (PairedGround n))
    (hl : l.Nodup) (g : MvPolynomial (PairedGround n) ℚ)
    (d : PairedGround n →₀ ℕ) (hd : ∀ j ∈ l, d j = 0) :
    (l.foldl (fun p j => extractLabel j p) g).coeff d =
      g.coeff (d + (l.map (fun j => Finsupp.single j 1)).sum) := by
  induction l generalizing g with
  | nil => simp
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hnodup.2 _ (fun s hs => hd s (by simp [hs]))]
    rw [extract_label_coefficient j _ _ (by
      rw [Finsupp.add_apply, hd j (by simp), single_list_sum_zero l j hnodup.1])]
    congr 1
    simp only [List.map_cons, List.sum_cons]
    ac_rfl

/-- INTERNAL: Embed the active old holes and two next-slot coordinates in the paired ground.
TEXLINE: main.tex:592-601 -/
noncomputable def activeLabel {n : ℕ} (R : PairedSet n) (t : Fin n) : R ⊕ Bool → PairedGround n :=
  Sum.elim Subtype.val (fun b => (t, b))

/-- INTERNAL: The exponent vector extracted from the ordinary slots.
TEXLINE: main.tex:587-589 -/
noncomputable def ordinarySlotExponent {n : ℕ} (U : Finset (Fin n)) (t : Fin n) : PairedGround n →₀ ℕ :=
  (((U.erase t).toList).map (fun s => Finsupp.single (s, false) 1)).sum

/-- INTERNAL: Preserve active labels and identify the labels of every ordinary slot.
TEXLINE: main.tex:587-589 -/
noncomputable def mergedLabel {n : ℕ} (R : PairedSet n) (t : Fin n) (e : PairedGround n) : PairedGround n :=
  if e ∈ R ∨ e.1 = t then e else (e.1, false)

/-- INTERNAL: Exact coefficient formula for the omitted-slot operations on an arbitrary input polynomial.
TEXLINE: main.tex:584-601 -/
lemma slot_extraction_coefficient {n : ℕ} (g : MvPolynomial (PairedGround n) ℚ)
    (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ) :
    (linearSubstitution (activeSubstitution R t)
      ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
        (linearSubstitution (slotSubstitution R U t)
          (differentiateLabels (fixedOmissions B R U) g)))).coeff d =
      ∑ v ∈ (differentiateLabels (fixedOmissions B R U)
        g).support,
        if (∀ e ∈ v.support, e ∈ R ∨ e.1 ∈ U) ∧
          v.mapDomain (mergedLabel R t) =
            d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then
          g.coeff
            (v + labelExponent (fixedOmissions B R U)) else 0 := by
  classical
  have hf : Function.Injective (activeLabel R t) := by
    intro i j hij
    cases i with
    | inl i =>
      cases j with
      | inl j => exact congrArg Sum.inl (Subtype.ext hij)
      | inr b =>
        have he : (i : PairedGround n) = (t, b) := hij
        exact False.elim ((hU t ht b).2 (he ▸ i.property))
    | inr b =>
      cases j with
      | inl j =>
        have he : (j : PairedGround n) = (t, b) := hij.symm
        exact False.elim ((hU t ht b).2 (he ▸ j.property))
      | inr c => exact congrArg Sum.inr (congrArg Prod.snd hij)
  have hweights : activeSubstitution R t =
      fun s j => if s = activeLabel R t j then (1 : ℚ) else 0 := by
    funext s j
    cases j <;> rfl
  have hzero : ∀ s ∈ (U.erase t).toList,
      (d.mapDomain (activeLabel R t)) (s, false) = 0 := by
    intro s hs
    have hst := Finset.mem_erase.mp (Finset.mem_toList.mp hs)
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨j, hj⟩
    cases j with
    | inl j =>
      exact (hU s hst.2 false).2 (hj ▸ j.property)
    | inr b =>
      exact hst.1 (congrArg Prod.fst hj).symm
  rw [hweights, restriction_coefficient _ hf]
  have hfold (g : MvPolynomial (PairedGround n) ℚ) :
      (U.erase t).toList.foldl (fun p s => extractLabel (s, false) p) g =
      ((U.erase t).toList.map (fun s => (s, false))).foldl (fun p e => extractLabel e p) g := by
    rw [List.foldl_map]
  rw [hfold, extract_labels_coefficient _ ((Finset.nodup_toList _).map
    (by intro i j h; exact congrArg Prod.fst h)) _ _ (by
      intro e he
      obtain ⟨s, hs, rfl⟩ := List.mem_map.mp he
      exact hzero s hs)]
  simp only [List.map_map]
  change (linearSubstitution (slotSubstitution R U t)
    (differentiateLabels (fixedOmissions B R U)
      g)).coeff
    (d.mapDomain (activeLabel R t) + ordinarySlotExponent U t) = _
  have hmask : slotSubstitution R U t =
      fun e f => if (e ∈ R ∨ e.1 ∈ U) ∧ mergedLabel R t e = f then (1 : ℚ) else 0 := by
    funext e f
    unfold slotSubstitution mergedLabel
    by_cases he : e ∈ R <;> by_cases het : e.1 = t <;>
      by_cases heu : e.1 ∈ U <;> simp_all
  rw [hmask, masked_substitution_coefficient]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases ha : (∀ e ∈ v.support, e ∈ R ∨ e.1 ∈ U) ∧
      v.mapDomain (mergedLabel R t) = d.mapDomain (activeLabel R t) + ordinarySlotExponent U t
  · rw [if_pos ha, if_pos ha]
    unfold differentiateLabels
    rw [derivative_list_coefficient _ (Finset.nodup_toList _) _ _ (by
      intro e he
      have hC := Finset.mem_toList.mp he
      have hn : e ∉ R ∧ e.1 ∉ U := by
        simp only [fixedOmissions, Finset.mem_sdiff, Finset.mem_univ, true_and,
          Finset.mem_union] at hC
        simp_all
      by_contra hne
      exact (ha.1 e (Finsupp.mem_support_iff.mpr hne)).elim hn.1 hn.2)]
    congr 1
    simp [labelExponent]
  · rw [if_neg ha, if_neg ha]

/-- INTERNAL: The omitted-slot extraction of a squarefree monomial has multiplicity one and the displayed surviving-pattern test.
TEXLINE: main.tex:584-601 -/
lemma slot_monomial_coefficient {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ)
    (A : PairedSet n) (c : ℚ) :
    (linearSubstitution (activeSubstitution R t)
      ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
        (linearSubstitution (slotSubstitution R U t)
          (differentiateLabels (fixedOmissions B R U)
            (MvPolynomial.monomial (labelExponent A) c))))).coeff d =
      if (fixedOmissions B R U) ⊆ A ∧
        (∀ e ∈ A \ fixedOmissions B R U, e ∈ R ∨ e.1 ∈ U) ∧
        (labelExponent (A \ fixedOmissions B R U)).mapDomain (mergedLabel R t) =
          d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then c else 0 := by
  classical
  rw [slot_extraction_coefficient _ B R U hU t ht]
  let C := fixedOmissions B R U
  let v₀ := labelExponent (A \ C)
  have hsupport (S : PairedSet n) (e : PairedGround n) :
      e ∈ (labelExponent S).support ↔ e ∈ S := by
    simp [Finsupp.mem_support_iff, label_exponent_apply]
  have hvzero : ∀ e ∈ C.toList, v₀ e = 0 := by
    intro e he
    simp [v₀, label_exponent_apply, Finset.mem_toList.mp he]
  change (∑ v ∈ (differentiateLabels C (MvPolynomial.monomial (labelExponent A) c)).support,
      if (∀ e ∈ v.support, e ∈ R ∨ e.1 ∈ U) ∧
          v.mapDomain (mergedLabel R t) = d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then
        (MvPolynomial.monomial (labelExponent A) c).coeff (v + labelExponent C) else 0) =
    if C ⊆ A ∧ (∀ e ∈ A \ C, e ∈ R ∨ e.1 ∈ U) ∧
        v₀.mapDomain (mergedLabel R t) = d.mapDomain (activeLabel R t) + ordinarySlotExponent U t then c else 0
  by_cases hCA : C ⊆ A
  · have hexp : v₀ + labelExponent C = labelExponent A := by
      ext e
      simp only [Finsupp.add_apply, v₀, label_exponent_apply, Finset.mem_sdiff]
      by_cases heC : e ∈ C
      · have heA := hCA heC
        simp [heC, heA]
      · by_cases heA : e ∈ A <;> simp [heC, heA]
    have heq (v : PairedGround n →₀ ℕ) :
        v + labelExponent C = labelExponent A ↔ v = v₀ := by
      rw [← hexp]
      exact add_right_cancel_iff
    have heq' (v : PairedGround n →₀ ℕ) : labelExponent A = v + labelExponent C ↔ v = v₀ :=
      eq_comm.trans (heq v)
    simp_rw [MvPolynomial.coeff_monomial, heq']
    rw [Finset.sum_eq_single v₀]
    · simp only [ite_and, if_pos hCA, v₀, hsupport, ite_true]
    · intro v hv hne
      simp [hne]
    · intro hnot
      have hd := MvPolynomial.notMem_support_iff.mp hnot
      unfold differentiateLabels at hd
      rw [derivative_list_coefficient C.toList (Finset.nodup_toList _) _ v₀ hvzero] at hd
      have hsum : (C.toList.map (fun e => Finsupp.single e 1)).sum = labelExponent C := by
        simp [labelExponent]
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

/-- INTERNAL: The precise omitted-label pattern selected by a requested active quadratic coefficient.
TEXLINE: main.tex:584-601 -/
noncomputable def SlotOmissionPattern {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n) (d : R ⊕ Bool →₀ ℕ) (state : PairedSet n) : Prop :=
  state.card = n ∧ fixedOmissions B R U ⊆ Finset.univ \ state ∧
    (∀ e ∈ (Finset.univ \ state) \ fixedOmissions B R U, e ∈ R ∨ e.1 ∈ U) ∧
    (labelExponent ((Finset.univ \ state) \ fixedOmissions B R U)).mapDomain (mergedLabel R t) =
      d.mapDomain (activeLabel R t) + ordinarySlotExponent U t

/-- INTERNAL: Expand the operational slot quadratic as a finite sum of rank weights over exactly the surviving omitted-label patterns.
TEXLINE: main.tex:584-601 -/
lemma slot_quadratic_state_sum {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ) :
    (operationalSlotQuadratic r o₁ o₂ q B R U t).coeff d =
      ∑ state : PairedSet n, if SlotOmissionPattern B R U t d state then
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) else 0 := by
  classical
  have hdiff (l : List (PairedGround n)) {β : Type} (S : Finset β)
      (f : β → MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p e => MvPolynomial.pderiv e p) (∑ z ∈ S, f z) =
        ∑ z ∈ S, l.foldl (fun p e => MvPolynomial.pderiv e p) (f z) := by
    induction l generalizing f with
    | nil => rfl
    | cons e l ih =>
      simp only [List.foldl_cons, map_sum]
      exact ih _
  have hextract (l : List (Fin n)) {β : Type} (S : Finset β)
      (f : β → MvPolynomial (PairedGround n) ℚ) :
      l.foldl (fun p s => extractLabel (s, false) p) (∑ z ∈ S, f z) =
        ∑ z ∈ S, l.foldl (fun p s => extractLabel (s, false) p) (f z) := by
    induction l generalizing f with
    | nil => rfl
    | cons e l ih =>
      simp only [List.foldl_cons]
      have hstep : extractLabel (e, false) (∑ z ∈ S, f z) =
          ∑ z ∈ S, extractLabel (e, false) (f z) := by
        simp [extractLabel, linearSubstitution, map_sum]
      rw [hstep, ih]
  have hzero (l : List (PairedGround n)) :
      l.foldl (fun p e => MvPolynomial.pderiv e p) 0 = (0 : MvPolynomial (PairedGround n) ℚ) := by
    induction l with
    | nil => rfl
    | cons e l ih => simpa using ih
  have hzero' (l : List (Fin n)) :
      l.foldl (fun p s => extractLabel (s, false) p) 0 = (0 : MvPolynomial (PairedGround n) ℚ) := by
    induction l with
    | nil => rfl
    | cons e l ih => simpa [extractLabel, linearSubstitution] using ih
  have hlabel (state : PairedSet n) :
      OmittedRankWeightPolynomial.omittedExponent state = labelExponent (Finset.univ \ state) := by
    ext e
    rw [label_exponent_apply, OmittedRankWeightPolynomial.omitted_exponent_apply]
    simp
  unfold operationalSlotQuadratic OmittedRankWeightPolynomial.omittedRankPolynomial
  simp only [differentiateLabels, hdiff, linearSubstitution, map_sum]
  change (linearSubstitution (activeSubstitution R t)
    ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
      (∑ state : PairedSet n, linearSubstitution (slotSubstitution R U t)
        ((fixedOmissions B R U).toList.foldl (fun p e => MvPolynomial.pderiv e p)
          (if state.card = n then MvPolynomial.monomial (OmittedRankWeightPolynomial.omittedExponent state)
            (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)) else 0))))).coeff d = _
  rw [hextract]
  simp only [linearSubstitution, map_sum, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hc : state.card = n
  · rw [if_pos hc, hlabel]
    change (linearSubstitution (activeSubstitution R t)
      ((U.erase t).toList.foldl (fun p s => extractLabel (s, false) p)
        (linearSubstitution (slotSubstitution R U t)
          (differentiateLabels (fixedOmissions B R U)
            (MvPolynomial.monomial (labelExponent (Finset.univ \ state))
              (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val))))))).coeff d = _
    rw [slot_monomial_coefficient B R U hU t ht]
    simp only [SlotOmissionPattern, hc, true_and]
  · rw [if_neg hc, hzero]
    simp only [map_zero, hzero', MvPolynomial.coeff_zero]
    rw [if_neg (by rintro ⟨h, _⟩; exact hc h)]
end CountingMatroid.Analysis.OmittedSlotCoefficientFormula
