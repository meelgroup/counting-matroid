import CountingMatroid.Analysis.ConditionalSelectedStateSum

set_option autoImplicit false

/-! Exact conversion of conditioned polynomial occupancy tests into the
operational ordered-defect and transversal totals, and exclusion of cubic
occupancy at a Boolean pair. -/

namespace CountingMatroid.Analysis.ConditionalOccupancyCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.ConditionalSelectedStateSum
open CountingMatroid.Analysis.OmittedTutteNormalization
open CountingMatroid.Analysis.TransversalPartition
open scoped BigOperators

/-- INTERNAL: At a respecting state, the exponent with one empty and one
full unassigned pair is exactly the executable classifier's defect test.
TEXLINE: main.tex:403-417 -/
theorem remaining_exponent_defect_iff {n : ℕ} (σ : Assignment n)
    (S : PairedSet n) (hS : Respects σ S) (a : DefectIndex n)
    (he : σ a.emptyPair = none) (hf : σ a.fullPair = none) :
    (labelExponent (S \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst =
        Finsupp.single a.fullPair 2 + ordinaryExponent σ {a.emptyPair, a.fullPair} ↔
      (classifyState S).val = .defect a.emptyPair a.fullPair := by
  classical
  rw [InitialMultipliersGood.classify_defect_iff]
  have hpoint (i : Fin n) :
      (labelExponent (S \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst i =
          (Finsupp.single a.fullPair 2 + ordinaryExponent σ {a.emptyPair, a.fullPair} : Fin n →₀ ℕ) i ↔
        (((i, false) ∉ S ∧ (i, true) ∉ S) ↔ i = a.emptyPair) ∧
        (((i, false) ∈ S ∧ (i, true) ∈ S) ↔ i = a.fullPair) := by
    rw [respects_occupancy_apply σ S hS, Finsupp.add_apply,
      Finsupp.single_apply, ordinary_exponent_apply]
    by_cases hie : i = a.emptyPair
    · subst i
      by_cases hx : (a.emptyPair, false) ∈ S <;>
        by_cases hy : (a.emptyPair, true) ∈ S <;>
          simp [he, hx, hy, a.distinct, a.distinct.symm]
    · by_cases hif : i = a.fullPair
      · subst i
        by_cases hx : (a.fullPair, false) ∈ S <;>
          by_cases hy : (a.fullPair, true) ∈ S <;>
            simp [hf, hx, hy, a.distinct, a.distinct.symm]
      · cases hσ : σ i with
        | none =>
          by_cases hx : (i, false) ∈ S <;>
            by_cases hy : (i, true) ∈ S <;>
              simp [hσ, hx, hy, hie, hif, Ne.symm hif]
        | some b =>
          have hb := hS i b hσ
          cases b <;> simp_all only [Bool.not_false, Bool.not_true]
          all_goals simp [hσ, hb.1, hb.2, hie, hif, Ne.symm hif]
  constructor
  · intro hd
    exact ⟨fun i => ((hpoint i).mp (DFunLike.congr_fun hd i)).1,
      fun i => ((hpoint i).mp (DFunLike.congr_fun hd i)).2⟩
  · rintro ⟨hE, hF⟩
    ext i
    exact (hpoint i).mpr ⟨hE i, hF i⟩

/-- INTERNAL: Convert the exact conditioned-state sum for a single ordered
empty/full pattern to its operational defect total.
TEXLINE: main.tex:403-417 -/
theorem operational_defect_coefficient {n : ℕ} (r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) (hq : 0 < q)
    (σ : Assignment n) (a : DefectIndex n)
    (he : σ a.emptyPair = none) (hf : σ a.fullPair = none) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single a.fullPair 2 + ordinaryExponent σ {a.emptyPair, a.fullPair}) =
      defectTotal r o₁ o₂ q σ a := by
  classical
  rw [conditioned_state_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq]
  unfold defectTotal
  apply Finset.sum_congr rfl
  intro S _
  by_cases hS : Respects σ S
  · simp only [remaining_exponent_defect_iff σ S hS a he hf]
    by_cases hk : (classifyState S).val = .defect a.emptyPair a.fullPair
    · have hc := OmittedRankWeightPolynomial.defect_card S a hk
      rw [if_pos ⟨hc, hS, hk⟩, if_pos ⟨hS, hk⟩]
    · rw [if_neg (by rintro ⟨_, _, h⟩; exact hk h),
        if_neg (by rintro ⟨_, h⟩; exact hk h)]
  · rw [if_neg (by rintro ⟨_, h, _⟩; exact hS h),
      if_neg (by rintro ⟨h, _⟩; exact hS h)]

/-- INTERNAL: The ordinary exponent test on a respecting state is exactly
one occupied label at every pair, including assigned pairs.
TEXLINE: main.tex:403-417 -/
theorem remaining_exponent_single_iff {n : ℕ} (σ : Assignment n)
    (S : PairedSet n) (hS : Respects σ S) :
    (labelExponent (S \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst =
        ordinaryExponent σ ∅ ↔
      ∀ i : Fin n, ((i, false) ∈ S ↔ (i, true) ∉ S) := by
  classical
  have hpoint (i : Fin n) :
      (labelExponent (S \ (selectedLabelList σ).toFinset)).mapDomain Prod.fst i =
          ordinaryExponent σ ∅ i ↔ ((i, false) ∈ S ↔ (i, true) ∉ S) := by
    rw [respects_occupancy_apply σ S hS, ordinary_exponent_apply]
    cases hσ : σ i with
    | none =>
      by_cases hx : (i, false) ∈ S <;> by_cases hy : (i, true) ∈ S <;>
        simp [hx, hy]
    | some b =>
      have hb := hS i b hσ
      cases b <;> simp_all only [Bool.not_false, Bool.not_true]
      all_goals simp [hb.1, hb.2]
  constructor
  · intro hd i
    exact (hpoint i).mp (DFunLike.congr_fun hd i)
  · intro hp
    ext i
    exact (hpoint i).mpr (hp i)

/-- INTERNAL: Reindex the exact single-occupancy coefficient by the existing
original-subset encoding of conditional transversals.
TEXLINE: main.tex:403-417 -/
theorem operational_transversal_coefficient {n : ℕ} (r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) (hq : 0 < q)
    (σ : Assignment n) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff (ordinaryExponent σ ∅) =
      transversalTotal r o₁ o₂ q σ := by
  classical
  rw [conditioned_state_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq]
  unfold transversalTotal
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun A _ => transversalState A)
  · intro A hA
    have hres := (subset_respects_iff σ A).mp (Finset.mem_filter.mp hA).2
    have hcard : (transversalState A).card = n := by
      unfold transversalState
      rw [Finset.card_image_of_injective _ (by
        intro i j h
        exact congrArg Prod.fst h)]
      simp
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨hcard, hres, (remaining_exponent_single_iff σ _ hres).mpr ?_⟩
    intro i
    simp [transversalState]
  · intro A _ B _ h
    ext i
    have hi := congrArg (fun S : PairedSet n => (i, false) ∈ S) h
    simpa [transversalState] using hi
  · intro S hS
    obtain ⟨_, hres, hd⟩ := (Finset.mem_filter.mp hS).2
    have hp := (remaining_exponent_single_iff σ S hres).mp hd
    let A := Finset.univ.filter (fun i : Fin n => (i, false) ∈ S)
    have heq : transversalState A = S := by
      ext ⟨i, b⟩
      cases b with
      | false => simp [transversalState, A]
      | true =>
        have hi : (i, true) ∈ S ↔ (i, false) ∉ S := by
          simpa only [not_not] using (not_congr (hp i)).symm
        simp [transversalState, A, hi]
    refine ⟨A, ?_, heq⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    apply (subset_respects_iff σ A).mpr
    rwa [heq]
  · intro A _
    rfl

/-- INTERNAL: Boolean paired sets have at most two labels at each pair, so
an exponent exceeding two has zero conditioned coefficient.
TEXLINE: main.tex:412-417 -/
theorem operational_cubic_coefficient {n : ℕ} (r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) (hq : 0 < q)
    (σ : Assignment n) (d : Fin n →₀ ℕ) (k : Fin n) (hd : 2 < d k) :
    (conditionedPairPolynomial M₁ M₂ q σ).coeff d = 0 := by
  classical
  rw [conditioned_state_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq]
  apply Finset.sum_eq_zero
  intro S _
  rw [if_neg]
  rintro ⟨_, _, he⟩
  have hk := DFunLike.congr_fun he k
  rw [occupancy_apply] at hk
  by_cases hx : (k, false) ∈ S \ (selectedLabelList σ).toFinset <;>
    by_cases hy : (k, true) ∈ S \ (selectedLabelList σ).toFinset <;>
      simp only [hx, hy, if_true, if_false] at hk <;> omega

end CountingMatroid.Analysis.ConditionalOccupancyCoefficients

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · exact defect and transversal occupancy conversions, finite transversal reindexing, and exclusion of coefficient exponents exceeding two at a pair.
-/
