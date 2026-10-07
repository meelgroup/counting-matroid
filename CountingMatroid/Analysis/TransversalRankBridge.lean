import CountingMatroid.Model.Subroutines
import CountingMatroid.Analysis.GreedyRankCorrect
import CountingMatroid.Analysis.TransversalProjection

set_option autoImplicit false

namespace CountingMatroid.Analysis.TransversalRankBridge

open CountingMatroid.Model

/-- INTERNAL: On a transversal, the concrete paired rank scan has zero
deficiency exactly at the common bases of the two original matroids.
TEXLINE: main.tex:244-293,1314-1320 -/
theorem transversal_rank_zero_iff_common_base (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (A : Finset (Fin n)) :
    n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
      (Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A))))).val = 0 ↔
      A ∈ commonBases M₁ M₂ := by
  classical
  have hscan₁ := GreedyRankCorrect.greedyRank_eq_eRk M₁ o₁ hfull.1 h₁ false A
  have hscan₂ := GreedyRankCorrect.greedyRank_eq_eRk M₂ o₂ hfull.2 h₂ true A
  unfold CountingMatroid.Model.Subroutines.pairedRank
  simp only [Arlib.Computation.Charged.val_bind,
    TransversalProjection.pairedProjections_transversal]
  simp only [CountingMatroid.Model.Operations.natSub,
    CountingMatroid.Model.Operations.natAdd, Arlib.Computation.Charged.val_op]
  have hk₁card : (CountingMatroid.Model.Subroutines.greedyRank false o₁ A).val ≤ A.card := by
    have h := M₁.eRk_le_encard (A : Set (Fin n))
    rw [← hscan₁] at h
    exact_mod_cast h
  have hk₂card : (CountingMatroid.Model.Subroutines.greedyRank true o₂ A).val ≤ A.card := by
    have h := M₂.eRk_le_encard (A : Set (Fin n))
    rw [← hscan₂] at h
    exact_mod_cast h
  rcases hr with ⟨hr₁, hr₂⟩
  have hk₁r : (CountingMatroid.Model.Subroutines.greedyRank false o₁ A).val ≤ r := by
    have h := M₁.eRk_le_eRank (A : Set (Fin n))
    rw [← hscan₁, hr₁] at h
    exact_mod_cast h
  have hk₂r : (CountingMatroid.Model.Subroutines.greedyRank true o₂ A).val ≤ r := by
    have h := M₂.eRk_le_eRank (A : Set (Fin n))
    rw [← hscan₂, hr₂] at h
    exact_mod_cast h
  have hcardn : A.card ≤ n := by
    simpa using Finset.card_le_card (Finset.subset_univ A)
  have hrn : r ≤ n := by
    have h := M₁.eRank_le_encard_ground
    rw [hr₁, hfull.1] at h
    have h' : (r : ℕ∞) ≤ (n : ℕ∞) := by simpa using h
    exact_mod_cast h'
  have hnumequiv :
      (n - ((CountingMatroid.Model.Subroutines.greedyRank false o₁ A).val +
          (n - A.card) +
          (CountingMatroid.Model.Subroutines.greedyRank true o₂ A).val - r) = 0) ↔
        A.card = r ∧
        (CountingMatroid.Model.Subroutines.greedyRank false o₁ A).val = r ∧
        (CountingMatroid.Model.Subroutines.greedyRank true o₂ A).val = r := by
    omega
  rw [hnumequiv]
  simp only [commonBases, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hcard, hk₁, hk₂⟩
    constructor
    · have hi : M₁.Indep (A : Set (Fin n)) := by
        apply (M₁.indep_iff_eRk_eq_encard_of_finite A.finite_toSet).2
        rw [← hscan₁, hk₁]
        simp [hcard]
      apply Matroid.isBasis_ground_iff.mp
      apply (M₁.isBasis_iff_indep_encard_eq_of_finite A.finite_toSet).2
      refine ⟨?_, hi, ?_⟩
      · rw [hfull.1]
        exact Set.subset_univ _
      · simp [hr₁, hcard]
    · have hi : M₂.Indep (A : Set (Fin n)) := by
        apply (M₂.indep_iff_eRk_eq_encard_of_finite A.finite_toSet).2
        rw [← hscan₂, hk₂]
        simp [hcard]
      apply Matroid.isBasis_ground_iff.mp
      apply (M₂.isBasis_iff_indep_encard_eq_of_finite A.finite_toSet).2
      refine ⟨?_, hi, ?_⟩
      · rw [hfull.2]
        exact Set.subset_univ _
      · simp [hr₂, hcard]
  · rintro ⟨hb₁, hb₂⟩
    have hcard : A.card = r := by
      have h := hb₁.encard_eq_eRank
      rw [hr₁] at h
      exact_mod_cast h
    refine ⟨hcard, ?_, ?_⟩
    · have h := hb₁.eRk_eq_eRank
      rw [← hscan₁, hr₁] at h
      exact_mod_cast h
    · have h := hb₂.eRk_eq_eRank
      rw [← hscan₂, hr₂] at h
      exact_mod_cast h

end CountingMatroid.Analysis.TransversalRankBridge

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · evaluated the transversal projections and greedy ranks, then reduced zero deficiency to two base conditions.
-/
