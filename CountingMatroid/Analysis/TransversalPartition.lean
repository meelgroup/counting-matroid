import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false

namespace CountingMatroid.Analysis.TransversalPartition

open CountingMatroid.Model

/-- INTERNAL: The paired state corresponding to an original-ground subset;
false marks its selected x elements and true marks its complementary y elements.
TEXLINE: main.tex:270-281 -/
def transversalState {n : ℕ} (A : Finset (Fin n)) : PairedSet n :=
  Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A)))

/-- INTERNAL: Rank deficiency of a transversal, calculated by the same paired
rank scan used by the bounded run.
TEXLINE: main.tex:292-316,1333-1346 -/
noncomputable def transversalDeficiency {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (A : Finset (Fin n)) : ℕ :=
  n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
    (transversalState A)).val

/-- INTERNAL: The paper's analytical transversal partition sum, expressed over
the concrete rank deficiencies used in `Program.weightOfKind`.
TEXLINE: main.tex:307-316 -/
noncomputable def partitionSum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) : ℚ :=
  ∑ A : Finset (Fin n), q ^ transversalDeficiency r o₁ o₂ A

/-- INTERNAL: At the final schedule parameter, common bases contribute one to
the transversal partition sum and every other transversal contributes at most
`q_L`. The concrete rank scan must agree with matroid rank for this comparison.
TEXLINE: main.tex:1314-1323 -/
theorem transversal_partition_contamination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let c := partitionSum r o₁ o₂ (s.ρ ^ s.L)
    (commonBaseCount M₁ M₂ : ℚ) ≤ c ∧
      c ≤ (1 + p.ε / 10) * (commonBaseCount M₁ M₂ : ℚ) := by
  -- BLOCKER: the concrete paired-rank scan has no correctness theorem against
  -- the two matroid ranks, so its zero deficiency cannot yet be identified
  -- with the common-base predicate. The schedule tail bound is also absent.
  sorry

end CountingMatroid.Analysis.TransversalPartition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · open · direct simplification exposes the missing paired-rank correctness theorem and the final schedule tail bound.
-/
