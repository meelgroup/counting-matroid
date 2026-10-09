import CountingMatroid.Analysis.OmittedSlotCoefficientFormula

set_option autoImplicit false

/-! The surviving omitted-label patterns in the slot quadratic are exactly
completions with two distinct active labels omitted. This is the combinatorial
coefficient identification in the transport Hessian. -/

namespace CountingMatroid.Analysis.SlotOmissionPatternCharacterization
open CountingMatroid.Model
open CountingMatroid.Analysis.OmittedSlotCoefficientFormula
open CountingMatroid.Analysis.OmittedSlotQuadratic
open CountingMatroid.Analysis.OmittedTutteNormalization
open scoped BigOperators
open Classical

/-- INTERNAL: Active coordinates have distinct paired labels. -/
lemma active_label_injective {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) : Function.Injective (activeLabel R t) := by
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

/-- INTERNAL: No allowed ordinary label is merged into an active label. -/
lemma merged_preimage_active {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (e : PairedGround n) (he : e ∈ R ∨ e.1 ∈ U)
    (k : R ⊕ Bool) : mergedLabel R t e = activeLabel R t k ↔ e = activeLabel R t k := by
  by_cases ha : e ∈ R ∨ e.1 = t
  · simp [mergedLabel, ha]
  · have heU : e.1 ∈ U := he.resolve_left (not_or.mp ha).1
    cases k with
    | inl k =>
      have hn : (e.1, false) ≠ (k : PairedGround n) := by
        intro h
        exact (hU e.1 heU false).2 (h ▸ k.property)
      have hn' : e ≠ (k : PairedGround n) := by
        intro h
        exact (not_or.mp ha).1 (h ▸ k.property)
      simp [mergedLabel, ha, activeLabel, hn, hn']
    | inr b =>
      have hn : (e.1, false) ≠ (t, b) := by
        intro h
        exact (not_or.mp ha).2 (congrArg Prod.fst h)
      have hn' : e ≠ (t, b) := by
        intro h
        exact (not_or.mp ha).2 (congrArg Prod.fst h)
      simp [mergedLabel, ha, activeLabel, hn, hn']

/-- INTERNAL: The merged exponent at an active label remains squarefree. -/
lemma merged_exponent_active {n : ℕ} (B R D : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (hD : ∀ e ∈ D, e ∈ R ∨ e.1 ∈ U) (k : R ⊕ Bool) :
    ((labelExponent D).mapDomain (mergedLabel R t)) (activeLabel R t k) =
      if activeLabel R t k ∈ D then 1 else 0 := by
  rw [labelExponent, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single, Finsupp.finset_sum_apply, Finsupp.single_apply]
  trans ∑ e ∈ D, if e = activeLabel R t k then (1 : ℕ) else 0
  · apply Finset.sum_congr rfl
    intro e he
    simp only [merged_preimage_active B R U hU t e (hD e he) k]
  · simp [eq_comm]

/-- INTERNAL: The ordinary extracted exponent is one at each false-label
representative and zero elsewhere. -/
lemma ordinary_exponent_apply {n : ℕ} (U : Finset (Fin n)) (t : Fin n)
    (e : PairedGround n) : ordinarySlotExponent U t e =
      if e.1 ∈ U.erase t ∧ e.2 = false then 1 else 0 := by
  have heq : ordinarySlotExponent U t =
      ∑ s ∈ U.erase t, (Finsupp.single (s, false) 1 : PairedGround n →₀ ℕ) := by
    simp [ordinarySlotExponent]
  rw [heq]
  rcases e with ⟨s, b⟩
  cases b <;> simp [Finsupp.single_apply, Prod.ext_iff]

/-- INTERNAL: An ordinary representative has exactly its two original
labels as preimages under slot merging. -/
lemma merged_preimage_ordinary {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t s : Fin n) (hs : s ∈ U.erase t) (e : PairedGround n) :
    mergedLabel R t e = (s, false) ↔ e.1 = s := by
  have hsU := (Finset.mem_erase.mp hs).2
  have hst := (Finset.mem_erase.mp hs).1
  have hf : (mergedLabel R t e).1 = e.1 := by
    unfold mergedLabel
    split_ifs <;> rfl
  constructor
  · intro he
    exact hf.symm.trans (congrArg Prod.fst he)
  · intro he
    have hnR : e ∉ R := by
      simpa only [← he, Prod.mk.eta] using (hU s hsU e.2).2
    have hnt : e.1 ≠ t := by simpa only [he] using hst
    simp [mergedLabel, hnR, hnt, he, hst]

/-- INTERNAL: At an ordinary representative the merged squarefree
exponent counts its two omitted labels. -/
lemma merged_exponent_ordinary {n : ℕ} (B R D : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t s : Fin n) (hs : s ∈ U.erase t) :
    ((labelExponent D).mapDomain (mergedLabel R t)) (s, false) =
      (if (s, false) ∈ D then 1 else 0) + (if (s, true) ∈ D then 1 else 0) := by
  rw [labelExponent, Finsupp.mapDomain_finsetSum]
  simp only [Finsupp.mapDomain_single, Finsupp.finsetSum_apply, Finsupp.single_apply]
  simp_rw [merged_preimage_ordinary B R U hU t s hs]
  trans ∑ e : PairedGround n, if e ∈ D then (if e.1 = s then 1 else 0) else 0
  · rw [← Finset.sum_subset (Finset.subset_univ D)]
    · apply Finset.sum_congr rfl
      intro e he
      rw [if_pos he]
    · intro e _ he
      rw [if_neg he]
  · rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_bool]
    rw [Finset.sum_eq_single s]
    · simp [add_comm]
    · intro i _ hi
      simp [hi]
    · simp

/-- INTERNAL: Active labels are never among the fixed omissions. -/
lemma active_label_not_fixed {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n) (ht : t ∈ U) (k : R ⊕ Bool) :
    activeLabel R t k ∉ fixedOmissions B R U := by
  cases k with
  | inl k => simp [activeLabel, fixedOmissions, k.property]
  | inr b => simp [activeLabel, fixedOmissions, ht]

/-- INTERNAL: The exponent test is equivalent to selecting fixed labels,
selecting the complement of the active exponents, and one label per ordinary slot.
TEXLINE: main.tex:584-601 -/
lemma pattern_iff_membership {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (d : R ⊕ Bool →₀ ℕ) (state : PairedSet n) :
    SlotOmissionPattern B R U t d state ↔
      state.card = n ∧ B ⊆ state ∧ state ⊆ B ∪ R ∪ U.product Finset.univ ∧
      (∀ k, (if activeLabel R t k ∈ state then 0 else 1) = d k) ∧
      (∀ s ∈ U.erase t, (s, false) ∈ state ↔ (s, true) ∉ state) := by
  have hf := active_label_injective B R U hU t ht
  have hordinary (s : Fin n) (hs : s ∈ U.erase t) (b : Bool) :
      (s, b) ∉ fixedOmissions B R U := by
    simp [fixedOmissions, (Finset.mem_erase.mp hs).2]
  have hrange (s : Fin n) (hs : s ∈ U.erase t) :
      (s, false) ∉ Set.range (activeLabel R t) := by
    rintro ⟨k, hk⟩
    cases k with
    | inl k => exact (hU s (Finset.mem_erase.mp hs).2 false).2 (hk ▸ k.property)
    | inr b => exact (Finset.mem_erase.mp hs).1 (congrArg Prod.fst hk).symm
  have hactord (k : R ⊕ Bool) : ordinarySlotExponent U t (activeLabel R t k) = 0 := by
    rw [ordinary_exponent_apply]
    cases k with
    | inl k =>
      apply if_neg
      rintro ⟨hk, hb⟩
      have he : (k : PairedGround n) = ((k : PairedGround n).1, false) := by
        exact Prod.ext rfl hb
      exact (hU k.val.1 (Finset.mem_erase.mp hk).2 false).2 (he ▸ k.property)
    | inr b => simp [activeLabel]
  constructor
  · rintro ⟨hc, hC, hD, heq⟩
    have hB : B ⊆ state := by
      intro e he
      by_contra hn
      have heC : e ∉ fixedOmissions B R U := by simp [fixedOmissions, he]
      have hd := hD e (by simp [hn, heC])
      rcases hd with hd | hd
      · exact Finset.disjoint_left.mp hBR he hd
      · exact (hU e.1 hd e.2).1 (by simpa using he)
    have hS : state ⊆ B ∪ R ∪ U.product Finset.univ := by
      intro e he
      by_contra hn
      have heC : e ∈ fixedOmissions B R U := by
        simpa only [fixedOmissions, Finset.mem_sdiff, Finset.mem_univ, true_and] using hn
      have hout := hC heC
      simpa [he] using hout
    refine ⟨hc, hB, hS, ?_, ?_⟩
    · intro k
      have hk := DFunLike.congr_fun heq (activeLabel R t k)
      rw [merged_exponent_active B R _ U hU t hD k,
        Finsupp.add_apply, Finsupp.mapDomain_apply hf, hactord, add_zero] at hk
      have hn := active_label_not_fixed B R U t ht k
      simpa [hn] using hk
    · intro s hs
      have hsEq := DFunLike.congr_fun heq (s, false)
      rw [merged_exponent_ordinary B R _ U hU t s hs, Finsupp.add_apply,
        Finsupp.mapDomain_of_notMem_range _ _ (hrange s hs),
        show ordinarySlotExponent U t (s, false) = 1 by simp [ordinary_exponent_apply, hs],
        zero_add] at hsEq
      have hn₀ := hordinary s hs false
      have hn₁ := hordinary s hs true
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hn₀, hn₁, not_false_eq_true,
        and_true] at hsEq
      by_cases ha : (s, false) ∈ state <;> by_cases hb : (s, true) ∈ state <;>
        simp only [ha, hb, not_true_eq_false, not_false_eq_true, ite_true, ite_false] at hsEq ⊢ <;> omega
  · rintro ⟨hc, hB, hS, ha, ho⟩
    have hC : fixedOmissions B R U ⊆ Finset.univ \ state := by
      intro e he
      have hn : e ∉ B ∪ R ∪ U.product Finset.univ := by
        simpa [fixedOmissions] using he
      simp only [Finset.mem_sdiff, Finset.mem_univ, true_and]
      exact fun h => hn (hS h)
    have hD : ∀ e ∈ (Finset.univ \ state) \ fixedOmissions B R U,
        e ∈ R ∨ e.1 ∈ U := by
      intro e he
      have hnS : e ∉ state := (Finset.mem_sdiff.mp (Finset.mem_sdiff.mp he).1).2
      have hnotC := (Finset.mem_sdiff.mp he).2
      have heT : e ∈ B ∪ R ∪ U.product Finset.univ := by
        by_contra hn
        exact hnotC (by
          simpa only [fixedOmissions, Finset.mem_sdiff, Finset.mem_univ, true_and] using hn)
      rcases Finset.mem_union.mp heT with heBR | heU
      · rcases Finset.mem_union.mp heBR with heB | heR
        · exact False.elim (hnS (hB heB))
        · exact Or.inl heR
      · exact Or.inr (Finset.mem_product.mp heU).1
    refine ⟨hc, hC, hD, ?_⟩
    ext e
    by_cases heR : e ∈ R
    · let k : R ⊕ Bool := Sum.inl ⟨e, heR⟩
      have hk : activeLabel R t k = e := rfl
      rw [← hk, merged_exponent_active B R _ U hU t hD k,
        Finsupp.add_apply, Finsupp.mapDomain_apply hf, hactord, add_zero]
      have hn := active_label_not_fixed B R U t ht k
      simpa [hn] using ha k
    · by_cases het : e.1 = t
      · let k : R ⊕ Bool := Sum.inr e.2
        have hk : activeLabel R t k = e := Prod.ext het.symm rfl
        rw [← hk, merged_exponent_active B R _ U hU t hD k,
          Finsupp.add_apply, Finsupp.mapDomain_apply hf, hactord, add_zero]
        have hn := active_label_not_fixed B R U t ht k
        simpa [hn] using ha k
      · by_cases heo : e.1 ∈ U.erase t ∧ e.2 = false
        · obtain ⟨hs, hb⟩ := heo
          have he : e = (e.1, false) := Prod.ext rfl hb
          rw [he, merged_exponent_ordinary B R _ U hU t e.1 hs, Finsupp.add_apply,
            Finsupp.mapDomain_of_notMem_range _ _ (hrange e.1 hs),
            show ordinarySlotExponent U t (e.1, false) = 1 by simp [ordinary_exponent_apply, hs],
            zero_add]
          have hn₀ := hordinary e.1 hs false
          have hn₁ := hordinary e.1 hs true
          simp only [Finset.mem_sdiff, Finset.mem_univ, true_and, hn₀, hn₁,
            not_false_eq_true, and_true]
          have ho' := ho e.1 hs
          by_cases h₀ : (e.1, false) ∈ state <;>
            by_cases h₁ : (e.1, true) ∈ state <;>
            simp [h₀, h₁] at ho' ⊢
        · rw [Finsupp.add_apply, ordinary_exponent_apply, if_neg heo]
          have hnr : e ∉ Set.range (activeLabel R t) := by
            rintro ⟨k, hk⟩
            cases k with
            | inl k => exact heR (hk ▸ k.property)
            | inr b => exact het (congrArg Prod.fst hk).symm
          rw [Finsupp.mapDomain_of_notMem_range _ _ hnr, zero_add]
          apply Finsupp.mapDomain_of_not_mem_image_support
          rintro ⟨f, hf, hfe⟩
          have hfD : f ∈ (Finset.univ \ state) \ fixedOmissions B R U := by
            simpa [Finsupp.mem_support_iff, label_exponent_apply] using hf
          have hfallowed := hD f hfD
          by_cases hfa : f ∈ R ∨ f.1 = t
          · have hfe' : f = e := by simpa [mergedLabel, hfa] using hfe
            rcases hfa with hfR | hft
            · exact heR (hfe' ▸ hfR)
            · exact het (hfe' ▸ hft)
          · have hfe' : (f.1, false) = e := by simpa [mergedLabel, hfa] using hfe
            apply heo
            refine ⟨?_, (congrArg Prod.snd hfe').symm⟩
            rw [← congrArg Prod.fst hfe']
            exact Finset.mem_erase.mpr ⟨(not_or.mp hfa).2,
              hfallowed.resolve_left (not_or.mp hfa).1⟩

/-- INTERNAL: An active completion has n selected labels after omitting
two distinct active labels.
TEXLINE: main.tex:589-601 -/
lemma active_completion_card {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (t : Fin n) (ht : t ∈ U) (i j : R ⊕ Bool) (hij : i ≠ j)
    (choices : Fin n → Bool) :
    (B ∪ ((R ∪ {(t, false), (t, true)}).erase (activeLabel R t i)).erase
      (activeLabel R t j) ∪ (U.erase t).image (fun s => (s, choices s))).card = n := by
  let A := R ∪ {(t, false), (t, true)}
  have hf := active_label_injective B R U hU t ht
  have hmem (k : R ⊕ Bool) : activeLabel R t k ∈ A := by
    cases k with
    | inl k => simp [A, activeLabel, k.property]
    | inr b => cases b <;> simp [A, activeLabel]
  have hdis : Disjoint B A := by
    rw [Finset.disjoint_left]
    intro e heB heA
    rcases Finset.mem_union.mp heA with heR | heT
    · exact Finset.disjoint_left.mp hBR heB heR
    · rcases Finset.mem_insert.mp heT with he | he
      · subst e
        exact (hU t ht false).1 heB
      · have he' := Finset.mem_singleton.mp he
        subst e
        exact (hU t ht true).1 heB
  have hdis' : Disjoint B ((A.erase (activeLabel R t i)).erase (activeLabel R t j)) :=
    hdis.mono_right ((Finset.erase_subset _ _).trans (Finset.erase_subset _ _))
  have hdisU : Disjoint (B ∪ (A.erase (activeLabel R t i)).erase (activeLabel R t j))
      ((U.erase t).image (fun s => (s, choices s))) := by
    rw [Finset.disjoint_left]
    intro e he hf'
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hf'
    obtain ⟨hst, hsU⟩ := Finset.mem_erase.mp hs
    rcases Finset.mem_union.mp he with heB | heA
    · exact (hU s hsU (choices s)).1 heB
    · have heA' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heA)
      rcases Finset.mem_union.mp heA' with heR | heT
      · exact (hU s hsU (choices s)).2 heR
      · have : s = t := by
          rcases Finset.mem_insert.mp heT with he | he
          · exact congrArg Prod.fst he
          · exact congrArg Prod.fst (Finset.mem_singleton.mp he)
        exact hst this
  have hcardA : A.card = R.card + 2 := by
    have heq : A = insert (t, false) (insert (t, true) R) := by
      ext e
      simp only [A, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
      tauto
    rw [heq, Finset.card_insert_of_notMem (by simp [(hU t ht false).2]),
      Finset.card_insert_of_notMem (hU t ht true).2]
  change (B ∪ (A.erase (activeLabel R t i)).erase (activeLabel R t j) ∪ _).card = n
  rw [Finset.card_union_of_disjoint hdisU, Finset.card_union_of_disjoint hdis',
    Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hf.ne hij.symm, hmem j⟩),
    Finset.card_erase_of_mem (hmem i), hcardA,
    Finset.card_image_of_injective _ (by intro s v h; exact congrArg Prod.fst h),
    Finset.card_erase_of_mem ht]
  have hpos : 0 < U.card := Finset.card_pos.mpr ⟨t, ht⟩
  omega

/-- INTERNAL: Membership in the chosen-label image is pointwise. -/
lemma mem_choice_image {n : ℕ} (S : Finset (Fin n)) (choices : Fin n → Bool)
    (e : PairedGround n) :
    e ∈ S.image (fun s => (s, choices s)) ↔ e.1 ∈ S ∧ choices e.1 = e.2 := by
  constructor
  · rintro he
    obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
    exact ⟨hs, rfl⟩
  · rintro ⟨hs, hb⟩
    exact Finset.mem_image.mpr ⟨e.1, hs, Prod.ext rfl hb⟩

/-- INTERNAL: An active coordinate is selected in the explicit completion
exactly when neither omission names that coordinate. -/
lemma active_completion_membership {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t : Fin n) (ht : t ∈ U) (i j k : R ⊕ Bool) (choices : Fin n → Bool) :
    activeLabel R t k ∈ B ∪ ((R ∪ {(t, false), (t, true)}).erase
      (activeLabel R t i)).erase (activeLabel R t j) ∪
      (U.erase t).image (fun s => (s, choices s)) ↔ k ≠ i ∧ k ≠ j := by
  have hf := active_label_injective B R U hU t ht
  have hnB : activeLabel R t k ∉ B := by
    cases k with
    | inl k => exact fun h => Finset.disjoint_left.mp hBR h k.property
    | inr b => exact (hU t ht b).1
  have hnU : (activeLabel R t k).1 ∉ U.erase t := by
    cases k with
    | inl k =>
      intro h
      exact (hU k.val.1 (Finset.mem_erase.mp h).2 k.val.2).2 (by simpa using k.property)
    | inr b => simp [activeLabel]
  have hA : activeLabel R t k ∈ R ∪ {(t, false), (t, true)} := by
    cases k with
    | inl k => simp [activeLabel, k.property]
    | inr b => cases b <;> simp [activeLabel]
  simp only [Finset.mem_union, Finset.mem_erase, hnB, false_or, hA, and_true,
    mem_choice_image, hnU, false_and, or_false, ne_eq, hf.eq_iff]
  tauto

/-- INTERNAL: The explicit completion selects exactly its chosen ordinary label. -/
lemma ordinary_completion_membership {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (t s : Fin n) (hs : s ∈ U.erase t) (i j : R ⊕ Bool)
    (choices : Fin n → Bool) (b : Bool) :
    (s, b) ∈ B ∪ ((R ∪ {(t, false), (t, true)}).erase
      (activeLabel R t i)).erase (activeLabel R t j) ∪
      (U.erase t).image (fun s => (s, choices s)) ↔ choices s = b := by
  have hnB := (hU s (Finset.mem_erase.mp hs).2 b).1
  have hnR := (hU s (Finset.mem_erase.mp hs).2 b).2
  have hst := (Finset.mem_erase.mp hs).1
  simp [Finset.mem_erase, mem_choice_image, hnB, hnR, Prod.ext_iff, hst, hs, (Finset.mem_erase.mp hs).2]

/-- PAPER: main.tex:592-601
A quadratic omitted-label pattern exists exactly for two distinct active
omissions, with all other active labels selected and one choice per ordinary slot. -/
lemma omission_pattern_iff {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ s ∈ U, ∀ b : Bool, (s, b) ∉ B ∧ (s, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (t : Fin n) (ht : t ∈ U) (i j : R ⊕ Bool) (state : PairedSet n) :
    SlotOmissionPattern B R U t (Finsupp.single i 1 + Finsupp.single j 1) state ↔
      i ≠ j ∧ ∃ choices : Fin n → Bool,
        state = B ∪ ((R ∪ {(t, false), (t, true)}).erase (activeLabel R t i)).erase
          (activeLabel R t j) ∪ (U.erase t).image (fun s => (s, choices s)) := by
  rw [pattern_iff_membership B R U hBR hU t ht]
  constructor
  · rintro ⟨hc, hB, hS, ha, ho⟩
    have hij : i ≠ j := by
      intro hij
      subst j
      have hi := ha i
      simp only [Finsupp.add_apply, Finsupp.single_eq_same] at hi
      split_ifs at hi <;> norm_num at hi
    have hactive (k : R ⊕ Bool) : activeLabel R t k ∈ state ↔ k ≠ i ∧ k ≠ j := by
      by_cases hki : k = i
      · subst k
        have hk := ha i
        by_cases hm : activeLabel R t i ∈ state <;>
          simp [Finsupp.add_apply, Finsupp.single_apply, hm, hij] at hk ⊢
      · by_cases hkj : k = j
        · subst k
          have hk := ha j
          by_cases hm : activeLabel R t j ∈ state <;>
            simp [Finsupp.add_apply, Finsupp.single_apply, hm, hij, hij.symm] at hk ⊢
        · have hk := ha k
          by_cases hm : activeLabel R t k ∈ state <;>
            simp [Finsupp.add_apply, Finsupp.single_apply, hki, hkj, hm, eq_comm] at hk ⊢
    let choices : Fin n → Bool := fun s => if (s, true) ∈ state then true else false
    have hchoice (s : Fin n) (hs : s ∈ U.erase t) (b : Bool) :
        (s, b) ∈ state ↔ choices s = b := by
      cases b
      · rw [ho s hs]
        simp [choices]
      · simp [choices]
    refine ⟨hij, choices, ?_⟩
    ext e
    by_cases heB : e ∈ B
    · have heS := hB heB
      simp [heB, heS]
    · by_cases heR : e ∈ R
      · let k : R ⊕ Bool := Sum.inl ⟨e, heR⟩
        have hk : activeLabel R t k = e := rfl
        calc
          (e ∈ state) ↔ k ≠ i ∧ k ≠ j := by simpa only [hk] using hactive k
          _ ↔ _ := by simpa only [hk] using
            (active_completion_membership B R U hBR hU t ht i j k choices).symm
      · by_cases het : e.1 = t
        · let k : R ⊕ Bool := Sum.inr e.2
          have hk : activeLabel R t k = e := Prod.ext het.symm rfl
          calc
            (e ∈ state) ↔ k ≠ i ∧ k ≠ j := by simpa only [hk] using hactive k
            _ ↔ _ := by simpa only [hk] using
              (active_completion_membership B R U hBR hU t ht i j k choices).symm
        · by_cases heU : e.1 ∈ U.erase t
          · calc
              (e ∈ state) ↔ choices e.1 = e.2 := by
                simpa only [Prod.mk.eta] using hchoice e.1 heU e.2
              _ ↔ _ := by simpa only [Prod.mk.eta] using
                (ordinary_completion_membership B R U hU t e.1 heU i j choices e.2).symm
          · have hnU : e.1 ∉ U := by
              intro h
              exact heU (Finset.mem_erase.mpr ⟨het, h⟩)
            have hnS : e ∉ state := by
              intro h
              have hh := hS h
              simp [heB, heR, hnU] at hh
            simp [hnS, heB, heR, Prod.ext_iff, het, mem_choice_image, heU, hnU]
  · rintro ⟨hij, choices, rfl⟩
    refine ⟨active_completion_card B R U hBR hU hsize t ht i j hij choices, ?_, ?_, ?_, ?_⟩
    · intro e he
      exact Finset.mem_union_left _ (Finset.mem_union_left _ he)
    · intro e he
      rcases Finset.mem_union.mp he with he | he
      · rcases Finset.mem_union.mp he with heB | heA
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ heB)
        · have heA' := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase heA)
          rcases Finset.mem_union.mp heA' with heR | heT
          · exact Finset.mem_union_left _ (Finset.mem_union_right _ heR)
          · have het : e.1 = t := by
              rcases Finset.mem_insert.mp heT with he | he
              · exact congrArg Prod.fst he
              · exact congrArg Prod.fst (Finset.mem_singleton.mp he)
            exact Finset.mem_union_right _ (Finset.mem_product.mpr
              ⟨het ▸ ht, Finset.mem_univ _⟩)
      · obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp he
        exact Finset.mem_union_right _ (Finset.mem_product.mpr
          ⟨(Finset.mem_erase.mp hs).2, Finset.mem_univ _⟩)
    · intro k
      simp only [active_completion_membership B R U hBR hU t ht i j k choices]
      by_cases hki : k = i <;> by_cases hkj : k = j <;>
        simp [Finsupp.add_apply, Finsupp.single_apply, hki, hkj, hij, eq_comm]
    · intro s hs
      rw [ordinary_completion_membership B R U hU t s hs i j choices false,
        ordinary_completion_membership B R U hU t s hs i j choices true]
      cases choices s <;> simp

end CountingMatroid.Analysis.SlotOmissionPatternCharacterization

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · characterized every surviving quadratic omission pattern as an explicit completion with two distinct active omissions; proved active squarefreeness, ordinary-slot selection, and the completion cardinality from the original node hypotheses.
-/
