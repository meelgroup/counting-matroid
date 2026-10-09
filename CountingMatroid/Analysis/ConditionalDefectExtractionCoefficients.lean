import CountingMatroid.Analysis.ConditionalDefectQuadratics
import Mathlib.Algebra.MvPolynomial.Rename
set_option autoImplicit false

/-! Exact coefficient calculus for the existing conditioned descendants.
The calculations below account for ordinary-pair extraction and retained
coordinate relabelling; operational rank-weight identities are separate. -/

namespace CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators

/-- INTERNAL: Deleting one variable preserves coefficients with zero exponent
in that variable. TEXLINE: main.tex:369-373 -/
private theorem deletion_coefficient {α : Type} [Fintype α] [DecidableEq α] (j : α)
    (g : MvPolynomial α ℚ) (d : α →₀ ℕ) (hd : d j = 0) :
    (linearSubstitution (fun s t => if s = j then 0 else if s = t then 1 else 0) g).coeff d =
      g.coeff d := by
  classical
  let f : {s : α // s ≠ j} → α := Subtype.val
  have hf : Function.Injective f := Subtype.val_injective
  have hsub : linearSubstitution
      (fun s t => if s = j then 0 else if s = t then 1 else 0) g =
      MvPolynomial.rename f (MvPolynomial.killCompl hf g) := by
    have hh : (MvPolynomial.aeval (fun s => ∑ t,
        MvPolynomial.C (if s = j then 0 else if s = t then 1 else 0 : ℚ) *
          MvPolynomial.X t)) = (MvPolynomial.rename f).comp (MvPolynomial.killCompl hf) := by
      apply MvPolynomial.algHom_ext
      intro s
      by_cases hs : s = j
      · subst s
        simp [MvPolynomial.killCompl, f]
      · have hr : s ∈ Set.range f := ⟨⟨s, hs⟩, rfl⟩
        simp [MvPolynomial.killCompl, hs, f]
        exact ((Equiv.ofInjective f hf).apply_symm_apply ⟨s, hr⟩).symm |> congrArg Subtype.val
    exact DFunLike.congr_fun hh g
  rw [hsub]
  let e := d.comapDomain f hf.injOn
  have hsupp : (↑d.support : Set α) ⊆ Set.range f := by
    intro s hs
    refine ⟨⟨s, ?_⟩, rfl⟩
    intro hsj
    subst s
    simp [hd] at hs
  have he : e.mapDomain f = d := d.mapDomain_comapDomain f hf hsupp
  rw [← he, MvPolynomial.coeff_rename_mapDomain f hf, MvPolynomial.coeff_killCompl]


/-- INTERNAL: Differentiating and deleting extracts exponent exactly one,
with no multiplicity. TEXLINE: main.tex:369-373 -/
theorem extract_one_coefficient {n : ℕ} (j : Fin n)
    (g : MvPolynomial (Fin n) ℚ) (d : Fin n →₀ ℕ) (hd : d j = 0) :
    (extractOne j g).coeff d = g.coeff (d + Finsupp.single j 1) := by
  unfold extractOne
  rw [deletion_coefficient j _ d hd, MvPolynomial.coeff_pderiv]
  simp [hd]

/-- INTERNAL: An extraction exponent vanishes outside its variable list. -/
private theorem single_list_sum_zero {α : Type} [DecidableEq α] (l : List α)
    (j : α) (hj : j ∉ l) :
    ((l.map (fun i => (Finsupp.single i 1 : α →₀ ℕ))).sum) j = 0 := by
  induction l with
  | nil => simp
  | cons i l ih =>
    simp only [List.mem_cons, not_or] at hj
    simp [hj.1, ih hj.2]

/-- INTERNAL: Distinct ordinary-pair extractions shift the requested
coefficient by one in every extracted variable. TEXLINE: main.tex:408-417 -/
theorem extract_list_coefficient {n : ℕ} (l : List (Fin n))
    (hl : l.Nodup) (g : MvPolynomial (Fin n) ℚ)
    (d : Fin n →₀ ℕ) (hd : ∀ j ∈ l, d j = 0) :
    (l.foldl (fun p j => extractOne j p) g).coeff d =
      g.coeff (d + (l.map (fun j => Finsupp.single j 1)).sum) := by
  induction l generalizing g with
  | nil => simp
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hnodup.2 _ (fun s hs => hd s (by simp [hs]))]
    rw [extract_one_coefficient j _ _ (by
      rw [Finsupp.add_apply, hd j (by simp), single_list_sum_zero l j hnodup.1])]
    congr 1
    simp only [List.map_cons, List.sum_cons]
    ac_rfl

/-- INTERNAL: Restricting to injectively relabelled coordinates extracts the
coefficient with zero exponents elsewhere. TEXLINE: main.tex:408-417 -/
theorem restriction_coefficient {α β : Type} [DecidableEq α] [Fintype β]
    (f : β → α) (hf : Function.Injective f) (g : MvPolynomial α ℚ)
    (d : β →₀ ℕ) :
    (linearSubstitution (fun s t => if s = f t then 1 else 0) g).coeff d =
      g.coeff (d.mapDomain f) := by
  classical
  have hsub : linearSubstitution (fun s t => if s = f t then 1 else 0) g =
      MvPolynomial.killCompl hf g := by
    have hh : (MvPolynomial.aeval (fun s => ∑ t,
        MvPolynomial.C (if s = f t then 1 else 0 : ℚ) * MvPolynomial.X t)) =
        MvPolynomial.killCompl hf := by
      apply MvPolynomial.algHom_ext
      intro s
      by_cases hs : s ∈ Set.range f
      · obtain ⟨t, rfl⟩ := hs
        simp [MvPolynomial.killCompl, hf.eq_iff, Equiv.ofInjective_symm_apply]
      · have hne (t : β) : s ≠ f t := fun h => hs ⟨t, h.symm⟩
        simp only [MvPolynomial.killCompl, MvPolynomial.aeval_X, dif_neg hs]
        simp [hne]
    exact DFunLike.congr_fun hh g
  rw [hsub, MvPolynomial.coeff_killCompl]


/-- INTERNAL: The exponent contributed by extracting every ordinary pair.
TEXLINE: main.tex:408-417 -/
noncomputable def ordinaryExponent {n : ℕ} (σ : Assignment n)
    (retained : Finset (Fin n)) : Fin n →₀ ℕ :=
  (((Finset.univ \ (assignedPairs σ ∪ retained)).toList).map
    (fun j => Finsupp.single j 1)).sum

/-- INTERNAL: Compute the retained polynomial's coefficient before relabelling.
TEXLINE: main.tex:408-417 -/
theorem retained_coefficient {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (retained : Finset (Fin n)) (d : Fin n →₀ ℕ)
    (hd : ∀ j ∈ Finset.univ \ (assignedPairs σ ∪ retained), d j = 0) :
    (retainedPolynomial M₁ M₂ q σ retained).coeff d =
      (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (d + ordinaryExponent σ retained) := by
  apply extract_list_coefficient _ (Finset.nodup_toList _) _ _
  simpa only [Finset.mem_toList] using hd

/-- INTERNAL: Compute each coefficient of the conditioned two-pair quadratic
as a coefficient of the polynomial before ordinary-pair extraction.
TEXLINE: main.tex:408-412 -/
theorem conditioned_pair_coefficient {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (i j : Fin n) (hij : i ≠ j)
    (d : Fin 2 →₀ ℕ) :
    (conditionedPairQuadratic M₁ M₂ q σ i j).coeff d =
      (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (d.mapDomain ![i, j] + ordinaryExponent σ {i, j}) := by
  classical
  have hf : Function.Injective (![i, j] : Fin 2 → Fin n) := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all
  have hweights : pairSubstitutionTwo i j =
      fun s t => if s = (![i, j] : Fin 2 → Fin n) t then 1 else 0 := by
    funext s t
    fin_cases t <;> by_cases hi : s = i <;> by_cases hj : s = j <;>
      simp_all [pairSubstitutionTwo]
  unfold conditionedPairQuadratic
  rw [hweights, restriction_coefficient _ hf]
  apply retained_coefficient
  intro s hs
  have hnot : s ∉ ({i, j} : Finset (Fin n)) := by
    exact fun h => (Finset.mem_sdiff.mp hs).2 (Finset.mem_union_right _ h)
  apply Finsupp.mapDomain_of_notMem_range
  rintro ⟨t, ht⟩
  fin_cases t <;> simp_all

/-- INTERNAL: The last derivative at k contributes its exact coefficient
multiplicity to the conditioned three-pair quadratic.
TEXLINE: main.tex:412-417 -/
theorem conditioned_triple_coefficient {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (i j k : Fin n)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (d : Fin 3 →₀ ℕ) :
    (conditionedTripleQuadratic M₁ M₂ q σ i j k).coeff d =
      (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (d.mapDomain ![i, j, k] + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) * (d 2 + 1) := by
  classical
  have hf : Function.Injective (![i, j, k] : Fin 3 → Fin n) := by
    intro s t h
    fin_cases s <;> fin_cases t <;> simp_all
  have hweights : tripleSubstitution i j k =
      fun s t => if s = (![i, j, k] : Fin 3 → Fin n) t then 1 else 0 := by
    funext s t
    fin_cases t <;> by_cases hi : s = i <;> by_cases hj : s = j <;>
      by_cases hk : s = k <;> simp_all [tripleSubstitution]
  unfold conditionedTripleQuadratic
  rw [hweights, restriction_coefficient _ hf, MvPolynomial.coeff_pderiv]
  have hkval : (d.mapDomain (![i, j, k] : Fin 3 → Fin n)) k = d 2 := by
    simpa using Finsupp.mapDomain_apply hf d 2
  rw [hkval, retained_coefficient]
  intro s hs
  have hnot : s ∉ ({i, j, k} : Finset (Fin n)) := by
    exact fun h => (Finset.mem_sdiff.mp hs).2 (Finset.mem_union_right _ h)
  have hzero : (d.mapDomain (![i, j, k] : Fin 3 → Fin n)) s = 0 := by
    apply Finsupp.mapDomain_of_notMem_range
    rintro ⟨t, ht⟩
    fin_cases t <;> simp_all
  have hsk : s ≠ k := by intro h; subst s; simp at hnot
  simp [Finsupp.add_apply, hzero, hsk]


/-- INTERNAL: Under pair identification, a coefficient is the sum over its
exponent preimages; variables set to zero must have zero exponent.
TEXLINE: main.tex:403-407 -/
theorem masked_substitution_coefficient {α β : Type} [DecidableEq β] [Fintype β]
    (active : α → Prop) [DecidablePred active] (f : α → β)
    (g : MvPolynomial α ℚ) (d : β →₀ ℕ) :
    (linearSubstitution (fun s t => if active s ∧ f s = t then 1 else 0) g).coeff d =
      ∑ u ∈ g.support,
        if (∀ s ∈ u.support, active s) ∧ u.mapDomain f = d then g.coeff u else 0 := by
  classical
  have hX (s : α) :
      (∑ t, MvPolynomial.C (if active s ∧ f s = t then 1 else 0 : ℚ) *
        (MvPolynomial.X t : MvPolynomial β ℚ)) =
        if active s then MvPolynomial.X (f s) else 0 := by
    by_cases h : active s <;> simp [h]
  have hmono (u : α →₀ ℕ) (c : ℚ) :
      linearSubstitution (fun s t => if active s ∧ f s = t then 1 else 0)
        (MvPolynomial.monomial u c) =
        if ∀ s ∈ u.support, active s then MvPolynomial.monomial (u.mapDomain f) c else 0 := by
    unfold linearSubstitution
    simp_rw [hX]
    by_cases ha : ∀ s ∈ u.support, active s
    · rw [if_pos ha, ← MvPolynomial.rename_monomial, MvPolynomial.rename_eq_aeval]
      rw [MvPolynomial.aeval_monomial, MvPolynomial.aeval_monomial]
      congr 1
      apply Finsupp.prod_congr
      intro s hs
      simp [ha s hs]
    · rw [if_neg ha, MvPolynomial.aeval_monomial, Finsupp.prod]
      push Not at ha
      obtain ⟨s, hs, hsa⟩ := ha
      rw [Finset.prod_eq_zero hs]
      · simp
      · simp [hsa, Finsupp.mem_support_iff.mp hs]
  have hpoly : linearSubstitution
      (fun s t => if active s ∧ f s = t then 1 else 0) g =
      ∑ u ∈ g.support, linearSubstitution
        (fun s t => if active s ∧ f s = t then 1 else 0)
        (MvPolynomial.monomial u (g.coeff u)) := by
    conv_lhs => rw [g.as_sum]
    unfold linearSubstitution
    rw [map_sum]
  rw [hpoly, MvPolynomial.coeff_sum]
  apply Finset.sum_congr rfl
  intro u hu
  rw [hmono]
  by_cases ha : ∀ s ∈ u.support, active s
  · rw [if_pos ha, MvPolynomial.coeff_monomial]
    by_cases heq : u.mapDomain f = d
    · rw [if_pos heq, if_pos ⟨ha, heq⟩]
    · rw [if_neg heq, if_neg (by rintro ⟨_, h⟩; exact heq h)]
  · rw [if_neg ha, MvPolynomial.coeff_zero,
      if_neg (by rintro ⟨h, _⟩; exact ha h)]


/-- INTERNAL: Delete the homogenizing variable and assigned-pair variables,
and identify each remaining label pair, with all coefficient multiplicities
computed by summing the surviving exponent preimages.
TEXLINE: main.tex:403-407 -/
theorem conditioned_substitution_coefficient {n : ℕ} (σ : Assignment n) (g : MvPolynomial (Option (PairedGround n)) ℚ)
    (d : Fin n →₀ ℕ) :
    (linearSubstitution (conditionedPairSubstitution σ) g).coeff d =
      ∑ u ∈ (MvPolynomial.killCompl (R := ℚ) (Option.some_injective (PairedGround n)) g).support,
        if (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d then
          g.coeff (u.mapDomain Option.some) else 0 := by
  classical
  have hsub : linearSubstitution (conditionedPairSubstitution σ) g =
      linearSubstitution (fun (e : PairedGround n) t => if σ e.1 = none ∧ e.1 = t then 1 else 0)
        (MvPolynomial.killCompl (R := ℚ) (Option.some_injective (PairedGround n)) g) := by
    have hh : MvPolynomial.aeval (fun s => ∑ t,
        MvPolynomial.C (conditionedPairSubstitution σ s t) *
          (MvPolynomial.X t : MvPolynomial (Fin n) ℚ)) =
        (MvPolynomial.aeval (fun e : PairedGround n => ∑ t,
          MvPolynomial.C (if σ e.1 = none ∧ e.1 = t then 1 else 0 : ℚ) *
            (MvPolynomial.X t : MvPolynomial (Fin n) ℚ))).comp (MvPolynomial.killCompl (R := ℚ) (Option.some_injective (PairedGround n))) := by
      apply MvPolynomial.algHom_ext
      intro s
      cases s with
      | none => simp [conditionedPairSubstitution, MvPolynomial.killCompl]
      | some e =>
        rcases e with ⟨i, b⟩
        cases b <;> simp [conditionedPairSubstitution, MvPolynomial.killCompl,
          Equiv.ofInjective_symm_apply]
    exact DFunLike.congr_fun hh g
  rw [hsub]
  rw [masked_substitution_coefficient]
  simp_rw [MvPolynomial.coeff_killCompl]


/-- INTERNAL: The selected-label derivatives before assigned-pair deletion
and pair identification, retaining the homogenizing variable.
TEXLINE: main.tex:354-367,403-407 -/
noncomputable def assignedDerivativeSource {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) : MvPolynomial (Option (PairedGround n)) ℚ :=
  (assignedPairs σ).toList.foldl
    (fun g i => MvPolynomial.pderiv (some (i, (σ i).getD false)) g)
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q))

/-- INTERNAL: Exact finite coefficient sum for the conditioned polynomial
before ordinary-pair extraction. This exposes the remaining operational
identity as a rank-weight and occupancy calculation, without assuming it.
TEXLINE: main.tex:354-367,403-407 -/
theorem conditioned_pair_coefficient_sum {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (d : Fin n →₀ ℕ) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff d =
      (q ^ n / (n.factorial : ℚ)) *
        ∑ u ∈ (MvPolynomial.killCompl (Option.some_injective (PairedGround n))
          (assignedDerivativeSource M₁ M₂ q σ)).support,
          if (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d then
            (assignedDerivativeSource M₁ M₂ q σ).coeff (u.mapDomain Option.some)
          else 0 := by
  unfold conditionedPairPolynomial
  rw [MvPolynomial.coeff_C_mul, conditioned_substitution_coefficient]
  rfl


/-- INTERNAL: Distinct selected-label derivatives extract squarefree selected
exponents without additional multiplicity when the remaining exponent is zero
at those labels. TEXLINE: main.tex:403-407 -/
theorem derivative_list_coefficient {α : Type} [DecidableEq α] (l : List α)
    (hl : l.Nodup) (g : MvPolynomial α ℚ) (d : α →₀ ℕ)
    (hd : ∀ j ∈ l, d j = 0) :
    (l.foldl (fun p j => MvPolynomial.pderiv j p) g).coeff d =
      g.coeff (d + (l.map (fun j => Finsupp.single j 1)).sum) := by
  induction l generalizing g with
  | nil => simp
  | cons j l ih =>
    have hnodup := List.nodup_cons.mp hl
    rw [List.foldl_cons, ih hnodup.2 _ (fun s hs => hd s (by simp [hs])),
      MvPolynomial.coeff_pderiv]
    have hz : (d + (l.map (fun s => Finsupp.single s 1)).sum : α →₀ ℕ) j = 0 := by
      rw [Finsupp.add_apply, hd j (by simp), single_list_sum_zero l j hnodup.1]
    rw [hz]
    simp only [List.map_cons, List.sum_cons]
    ac_rfl

/-- INTERNAL: Extracting a zero remaining homogenizer exponent after n
homogenizing derivatives contributes exactly n!.
TEXLINE: main.tex:354-367 -/
theorem homogenizer_derivative_coefficient {α : Type} [DecidableEq α]
    (j : α) (g : MvPolynomial α ℚ) (d : α →₀ ℕ) (hd : d j = 0) (m : ℕ) :
    ((MvPolynomial.pderiv j)^[m] g).coeff d =
      g.coeff (d + Finsupp.single j m) * (m.factorial : ℚ) := by
  induction m generalizing g with
  | zero => simp
  | succ m ih =>
    rw [Function.iterate_succ_apply, ih, MvPolynomial.coeff_pderiv]
    have hexp : d + Finsupp.single j m + Finsupp.single j 1 =
        d + Finsupp.single j (m + 1) := by
      rw [add_assoc, ← Finsupp.single_add]
    rw [hexp]
    simp [Finsupp.add_apply, hd, Nat.factorial_succ]
    ring


/-- INTERNAL: The selected label exponents specified by the assignment.
TEXLINE: main.tex:403-407 -/
noncomputable def assignedExponent {n : ℕ} (σ : Assignment n) :
    Option (PairedGround n) →₀ ℕ :=
  ((assignedPairs σ).toList.map
    (fun i => Finsupp.single (some (i, (σ i).getD false)) 1)).sum

/-- INTERNAL: Evaluate all selected-label and homogenizing derivatives at
an exponent supported only on unassigned pairs. The remaining coefficient
is a coefficient of the original Tutte polynomial, times exactly n!.
TEXLINE: main.tex:354-367,403-407 -/
theorem assigned_source_coefficient {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (u : PairedGround n →₀ ℕ)
    (ha : ∀ e ∈ u.support, σ e.1 = none) :
    (assignedDerivativeSource M₁ M₂ q σ).coeff (u.mapDomain Option.some) =
      (tuttePolynomial (pairedMatroid M₁ M₂) q).coeff
        (u.mapDomain Option.some + assignedExponent σ + Finsupp.single none n) *
          (n.factorial : ℚ) := by
  classical
  let label : Fin n → Option (PairedGround n) :=
    fun i => some (i, (σ i).getD false)
  have hinj : Function.Injective label := by
    intro i j h
    exact congrArg Prod.fst (Option.some.inj h)
  let l := (assignedPairs σ).toList.map label
  have hl : l.Nodup := (Finset.nodup_toList _).map hinj
  have hd : ∀ e ∈ l, (u.mapDomain Option.some) e = 0 := by
    intro e he
    obtain ⟨i, hi, rfl⟩ := List.mem_map.mp he
    rw [Finsupp.mapDomain_apply (Option.some_injective (PairedGround n))]
    by_contra hne
    have hz := ha (i, (σ i).getD false) (Finsupp.mem_support_iff.mpr hne)
    exact (Finset.mem_filter.mp (Finset.mem_toList.mp hi)).2 hz
  have hfold : assignedDerivativeSource M₁ M₂ q σ =
      l.foldl (fun p e => MvPolynomial.pderiv e p)
        ((MvPolynomial.pderiv none)^[n] (tuttePolynomial (pairedMatroid M₁ M₂) q)) := by
    simp [assignedDerivativeSource, l, label, List.foldl_map]
  rw [hfold, derivative_list_coefficient l hl _ _ hd]
  have hexp : (l.map (fun e => Finsupp.single e 1)).sum = assignedExponent σ := by
    simp [assignedExponent, l, label, List.map_map]
  rw [hexp]

  apply homogenizer_derivative_coefficient
  have hnone : none ∉ l := by
    rintro h
    obtain ⟨i, hi, heq⟩ := List.mem_map.mp h
    cases heq
  have hz := single_list_sum_zero l none hnone
  rw [← hexp]
  change (u.mapDomain Option.some +
    (l.map (fun e => Finsupp.single e 1)).sum : Option (PairedGround n) →₀ ℕ) none = 0
  rw [Finsupp.add_apply, hz,
    Finsupp.mapDomain_of_notMem_range u none (by rintro ⟨e, he⟩; cases he)]

/-- INTERNAL: The normalization q^n/n! cancels the homogenizing derivative
multiplicity exactly. Every surviving coefficient is now a coefficient of
Tutte at the prescribed selected-label and homogenizer exponents.
TEXLINE: main.tex:354-367,403-407 -/
theorem conditioned_pair_tutte_coefficient_sum {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (q : ℚ) (σ : Assignment n) (d : Fin n →₀ ℕ) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff d =
      q ^ n * ∑ u ∈ (MvPolynomial.killCompl (Option.some_injective (PairedGround n))
        (assignedDerivativeSource M₁ M₂ q σ)).support,
        if (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d then
          (tuttePolynomial (pairedMatroid M₁ M₂) q).coeff
            (u.mapDomain Option.some + assignedExponent σ + Finsupp.single none n)
        else 0 := by
  classical
  rw [conditioned_pair_coefficient_sum]
  have hterm (u : PairedGround n →₀ ℕ) :
      (if (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d then
        (assignedDerivativeSource M₁ M₂ q σ).coeff (u.mapDomain Option.some) else 0) =
      (if (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d then
        (tuttePolynomial (pairedMatroid M₁ M₂) q).coeff
          (u.mapDomain Option.some + assignedExponent σ + Finsupp.single none n)
        else 0) * (n.factorial : ℚ) := by
    by_cases h : (∀ e ∈ u.support, σ e.1 = none) ∧ u.mapDomain Prod.fst = d
    · rw [if_pos h, if_pos h, assigned_source_coefficient M₁ M₂ q σ u h.1]
    · rw [if_neg h, if_neg h, zero_mul]
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  have hf : (n.factorial : ℚ) ≠ 0 := by positivity
  field_simp

end CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
