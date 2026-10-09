import CountingMatroid.Analysis.DefectSlotRoot

set_option autoImplicit false

/-!
Operational class labels at terminal vertices of the defect/event slot
configuration. The base holds one label at pair k, the root holes hold its
mate and the prescribed pair-i label, and all ordinary pairs have one label.
-/

namespace CountingMatroid.Analysis.DefectLeafClassifier

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.LeafCliqueFlow
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: Explicit occupancy of a terminal vertex, before the
executable classifier's pair scan is evaluated.
TEXLINE: main.tex:875-897 -/
theorem defect_leaf_membership {n : ℕ} (i k : Fin n) (a b : Bool)
    (R : PairedSet n) (choices : Fin n → Bool)
    (hR : R = {(i, !a), (k, b)} ∪
      ((Finset.univ.erase i).erase k).image (fun t => (t, choices t)))
    (hole : R) (t : Fin n) (c : Bool) :
    (t, c) ∈ leafVertex {(k, !b)} R hole ↔
      (t = k ∧ c = !b) ∨
      ((t, c) ≠ hole.val ∧ ((t = i ∧ c = !a) ∨ (t = k ∧ c = b) ∨
        (t ≠ i ∧ t ≠ k ∧ c = choices t))) := by
  classical
  unfold leafVertex
  simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_erase, hR]
  have him : (t, c) ∈ ((Finset.univ.erase i).erase k).image
      (fun s => (s, choices s)) ↔ t ≠ i ∧ t ≠ k ∧ c = choices t := by
    constructor
    · intro hh
      obtain ⟨s, hs, he⟩ := Finset.mem_image.mp hh
      have hst : s = t := congrArg Prod.fst he
      subst s
      obtain ⟨htk, hti, _⟩ := Finset.mem_erase.mp hs |>.imp_right Finset.mem_erase.mp
      exact ⟨hti, htk, (congrArg Prod.snd he).symm⟩
    · rintro ⟨hti, htk, hc⟩
      exact Finset.mem_image.mpr ⟨t, by simp [hti, htk], Prod.ext rfl hc.symm⟩
  rw [him]
  simp only [Finset.mem_insert, Finset.mem_singleton, Prod.mk.injEq]
  tauto

/-- PAPER: main.tex:875-897
Removing the pair-k root hole gives a transversal. Every other terminal
hole gives the ordered defect with that hole's original pair empty and
pair k doubled. This classification identifies the operational multiplier. -/
theorem defect_leaf_classifier {n : ℕ} (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (R : PairedSet n) (choices : Fin n → Bool)
    (hR : R = {(i, !a), (k, b)} ∪
      ((Finset.univ.erase i).erase k).image (fun t => (t, choices t))) (hole : R) :
    (classifyState (leafVertex {(k, !b)} R hole)).val =
      if hole.val.1 = k then .transversal else .defect hole.val.1 k := by
  classical
  have hm := defect_leaf_membership i k a b R choices hR hole
  by_cases hk : hole.val.1 = k
  · rw [if_pos hk]
    have hehole : hole.val = (k, b) := by
      have hh : hole.val ∈ ({(i, !a), (k, b)} : PairedSet n) ∪
          ((Finset.univ.erase i).erase k).image (fun t => (t, choices t)) :=
        Eq.mp (congrArg (fun S : PairedSet n => hole.val ∈ S) hR) hole.property
      rcases Finset.mem_union.mp hh with hh | hh
      · rcases Finset.mem_insert.mp hh with hi | hh
        · have he : i = k := (congrArg Prod.fst hi).symm.trans hk
          exact False.elim (hik he)
        · exact Finset.mem_singleton.mp hh
      · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hh
        have htk : t = k := (congrArg Prod.fst he).trans hk
        exact False.elim ((Finset.ne_of_mem_erase ht) htk)
    have himage : (k, b) ∉ ((Finset.univ.erase i).erase k).image (fun t => (t, choices t)) := by
      intro hh
      obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hh
      exact (Finset.ne_of_mem_erase ht) (congrArg Prod.fst he)
    have hs : SlotCompletion {(k, !b)} {(i, !a), (k, b)}
        ((Finset.univ.erase i).erase k) (k, b) (leafVertex {(k, !b)} R hole) := by
      refine ⟨choices, ?_⟩
      simp only [leafVertex, hehole, hR, Finset.erase_union_distrib,
        Finset.erase_eq_of_notMem himage, Finset.union_assoc]
    have hevent := (DefectSlotRoot.event_completion_iff i k hik a b _).mp hs
    exact (Finset.mem_filter.mp hevent).2.1
  · rw [if_neg hk]
    apply (InitialMultipliersGood.classify_defect_iff _ ⟨hole.val.1, k, hk⟩).mpr
    have hselected : hole.val.2 = (if hole.val.1 = i then !a else choices hole.val.1) := by
      have hh : hole.val ∈ ({(i, !a), (k, b)} : PairedSet n) ∪
          ((Finset.univ.erase i).erase k).image (fun t => (t, choices t)) :=
        Eq.mp (congrArg (fun S : PairedSet n => hole.val ∈ S) hR) hole.property
      rcases Finset.mem_union.mp hh with hh | hh
      · rcases Finset.mem_insert.mp hh with hi | hh
        · rw [hi]
          simp
        · have he := congrArg Prod.fst (Finset.mem_singleton.mp hh)
          exact False.elim (hk he)
      · obtain ⟨t, ht, he⟩ := Finset.mem_image.mp hh
        have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        have hfst : t = hole.val.1 := congrArg Prod.fst he
        have hbit : choices t = hole.val.2 := congrArg Prod.snd he
        rw [← hfst, if_neg hti]
        exact hbit.symm
    have hs (c : Bool) : (hole.val.1, c) ∉ leafVertex {(k, !b)} R hole := by
      intro hh
      rw [hm] at hh
      have heq : (hole.val.1, c) ≠ hole.val ↔ c ≠ hole.val.2 := by
        rw [← Prod.eta hole.val]
        simp only [ne_eq, Prod.mk.injEq, true_and]
      rw [heq] at hh
      by_cases hi : hole.val.1 = i
      · simp [hi, hik] at hh hselected
        exact hh.1 (hh.2.trans hselected.symm)
      · simp [hi, hk] at hh hselected
        exact hh.1 (hh.2.trans hselected.symm)
    have hfull (c : Bool) : (k, c) ∈ leafVertex {(k, !b)} R hole := by
      rw [hm]
      have hn : (k, c) ≠ hole.val := fun he => hk (congrArg Prod.fst he).symm
      cases b <;> cases c <;> simp [hn, Ne.symm hik]
    have hpair (t : Fin n) (hts : t ≠ hole.val.1) (htk : t ≠ k) :
        (t, false) ∈ leafVertex {(k, !b)} R hole ↔
          (t, true) ∉ leafVertex {(k, !b)} R hole := by
      rw [hm, hm]
      have hn (c : Bool) : (t, c) ≠ hole.val := fun he => hts (congrArg Prod.fst he)
      by_cases hti : t = i
      · subst t
        cases a <;> simp [hn, hik]
      · cases choices t <;> simp [hn, hti, htk]
    constructor
    · intro t
      by_cases hts : t = hole.val.1
      · subst t
        simp only [iff_true]
        exact ⟨hs false, hs true⟩
      · rw [iff_false_intro hts]
        refine ⟨?_, False.elim⟩
        rintro ⟨hx, hy⟩
        by_cases htk : t = k
        · subst t
          exact hx (hfull false)
        · exact hx ((hpair t hts htk).mpr hy)
    · intro t
      by_cases htk : t = k
      · subst t
        simp only [iff_true]
        exact ⟨hfull false, hfull true⟩
      · rw [iff_false_intro htk]
        refine ⟨?_, False.elim⟩
        rintro ⟨hx, hy⟩
        by_cases hts : t = hole.val.1
        · subst t
          exact hs false hx
        · exact (hpair t hts htk).mp hx hy

/-- INTERNAL: Translate the terminal class label into its actual program
weight and normalized operational vertex capacity.
TEXLINE: main.tex:721-728,875-897 -/
theorem defect_leaf_operational_weight {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (R : PairedSet n) (choices : Fin n → Bool)
    (hR : R = {(i, !a), (k, b)} ∪
      ((Finset.univ.erase i).erase k).image (fun t => (t, choices t))) (hole : R) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let Z : ℝ := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
    let W : PairedGround n → ℝ := fun e => if e.1 = i then (w ⟨i, k, hik⟩ : ℝ)
      else if h : e.1 = k then 1 else (w ⟨e.1, k, h⟩ : ℝ)
    W hole * slotTotal r o₁ o₂ q {(k, !b)} R ∅ hole =
      Z * π (leafVertex {(k, !b)} R hole) := by
  classical
  intro π Z W
  let S := leafVertex {(k, !b)} R hole
  let f := q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ S).val)
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw).1
  have hslot : slotTotal r o₁ o₂ q {(k, !b)} R ∅ hole = (f : ℝ) := by
    simp [slotTotal, SlotCompletion, f, S, leafVertex]
  have hkind := defect_leaf_classifier i k hik a b R choices hR hole
  have hweight : (StationaryMeanIdentities.stateWeight r o₁ o₂ q w S : ℝ) = W hole * (f : ℝ) := by
    by_cases hk : hole.val.1 = k
    · rw [if_pos hk] at hkind
      have hwi : W hole = 1 := by simp [W, hk, Ne.symm hik]
      rw [hwi, one_mul]
      simp [StationaryMeanIdentities.stateWeight, S, hkind, weightOfKind,
        Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value, f]
    · rw [if_neg hk] at hkind
      have hsw : StationaryMeanIdentities.stateWeight r o₁ o₂ q w S =
          w ⟨hole.val.1, k, hk⟩ * f := by
        simp [StationaryMeanIdentities.stateWeight, S, hkind, weightOfKind, hk,
          Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value,
          Model.Operations.multiplierRead, Model.Operations.ratMul, f]
      rw [hsw, Rat.cast_mul]
      by_cases hi : hole.val.1 = i
      · have hindex : (⟨hole.val.1, k, hk⟩ : DefectIndex n) = ⟨i, k, hik⟩ := by
          cases hi
          rfl
        rw [hindex]
        simp only [W, if_pos hi]
      · simp only [W, if_neg hi, dif_neg hk]
  rw [hslot]
  change W hole * (f : ℝ) = Z * ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w S : ℝ) / Z)
  rw [mul_div_cancel₀ _ hZ.ne', hweight]

end CountingMatroid.Analysis.DefectLeafClassifier
