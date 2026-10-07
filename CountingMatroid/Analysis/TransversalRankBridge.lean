import CountingMatroid.Model.Subroutines

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
  unfold CountingMatroid.Model.Subroutines.pairedRank
  simp only [Arlib.Computation.Charged.val_bind]
  -- BLOCKER: `pairedRank` is a charged fold of two `greedyRank` scans.
  -- Neither the concrete scan's rank correctness nor its projection equation
  -- is supplied by Model/Subroutines or the pinned matroid library.
  sorry

end CountingMatroid.Analysis.TransversalRankBridge
