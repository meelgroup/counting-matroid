import CountingMatroid.Analysis.IntersectionSearch

set_option autoImplicit false

/-!
Correctness obligation for the concrete capped exchange-path augmentation.
The query predicates are verified in `IntersectionSearch`. The remaining
mathematics is shortest-path exchange preservation and the separating rank
certificate when no source-to-sink path exists. This is an internal refinement
of the cited pretest, not an additional oracle or an assumed contract.
-/

namespace CountingMatroid.Analysis.IntersectionAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Two complementary rank certificates bound every common
independent competitor. This is the last arithmetic step of the no-path
maximality argument; graph nonreachability must establish the two bases.
TEXLINE: main.tex:283-289 -/
theorem separator_card_le {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (I R : Finset (Fin n))
    (hfirst : M₁.IsBasis ((I \ R : Finset (Fin n)) : Set (Fin n))
      ((Finset.univ \ R : Finset (Fin n)) : Set (Fin n)))
    (hsecond : M₂.IsBasis ((I ∩ R : Finset (Fin n)) : Set (Fin n))
      (R : Set (Fin n)))
    (J : Finset (Fin n)) (hJ₁ : M₁.Indep (J : Set (Fin n)))
    (hJ₂ : M₂.Indep (J : Set (Fin n))) : J.card ≤ I.card := by
  have hdiffIndep : M₁.Indep ((J \ R : Finset (Fin n)) : Set (Fin n)) :=
    hJ₁.subset (by simp only [Finset.coe_sdiff]; exact Set.sdiff_subset)
  have hdiffSubset : ((J \ R : Finset (Fin n)) : Set (Fin n)) ⊆
      ((Finset.univ \ R : Finset (Fin n)) : Set (Fin n)) := by
    intro i hi
    change i ∈ J \ R at hi
    change i ∈ Finset.univ \ R
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ i, (Finset.mem_sdiff.mp hi).2⟩
  have hdiff := hdiffIndep.encard_le_eRk_of_subset hdiffSubset
  rw [← hfirst.encard_eq_eRk] at hdiff
  have hdiffCard : (J \ R).card ≤ (I \ R).card := by
    simpa only [Set.encard_coe_eq_coe_finsetCard, ENat.coe_le_coe] using hdiff
  have hinterIndep : M₂.Indep ((J ∩ R : Finset (Fin n)) : Set (Fin n)) :=
    hJ₂.subset (by simp only [Finset.coe_inter]; exact Set.inter_subset_left)
  have hinter := hinterIndep.encard_le_eRk_of_subset
    (show ((J ∩ R : Finset (Fin n)) : Set (Fin n)) ⊆ (R : Set (Fin n)) by
      simp only [Finset.coe_inter]; exact Set.inter_subset_right)
  rw [← hsecond.encard_eq_eRk] at hinter
  have hinterCard : (J ∩ R).card ≤ (I ∩ R).card := by
    simpa only [Set.encard_coe_eq_coe_finsetCard, ENat.coe_le_coe] using hinter
  have hJpart := Finset.card_sdiff_add_card_inter J R
  have hIpart := Finset.card_sdiff_add_card_inter I R
  omega

/-- INTERNAL: A concrete shortest-path augmentation either increases common
independence by one element or leaves a maximum common independent set fixed.
This separates the mathematical exchange argument from the independent
unconditional resource accounting for exactly the same implementation.
TEXLINE: main.tex:283-289 -/
theorem augmentation_progress {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) :
    let next := (augmentOnce o₁ o₂ I).val
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      (next.card = I.card + 1 ∨
        (next = I ∧ ∀ J : Finset (Fin n),
          M₁.Indep (J : Set (Fin n)) → M₂.Indep (J : Set (Fin n)) → J.card ≤ I.card)) := by
  dsimp only
  unfold augmentOnce
  simp only [Arlib.Computation.Charged.val_bind]
  cases hp : (findPath (buildGraph o₁ o₂ I).val).val with
  | none =>
    simp only [Arlib.Computation.Charged.val_pure]
    refine ⟨hI₁, hI₂, Or.inr ⟨trivial, ?_⟩⟩
    intro J hJ₁ hJ₂
    let graph := (buildGraph o₁ o₂ I).val
    let paths := (Arlib.Computation.Charged.foldl
      (fun paths (_ : ℕ) => relaxPaths graph paths) (List.range n)
      (initialPaths graph).val).val
    let reachable := Finset.univ.filter (fun i => (paths i).isSome)
    refine separator_card_le M₁ M₂ I reachable ?_ ?_ J hJ₁ hJ₂
    · -- BLOCKER: the first-matroid basis certificate on the complement of
      -- the final BFS-reachable set. Its fundamental circuits cannot cross
      -- from reachable inside vertices to unreachable outside vertices.
      -- `hp` rules out any reachable second-matroid sink. The arithmetic
      -- comparison with J is already discharged by `separator_card_le`.
      sorry
    · -- BLOCKER: the second-matroid basis certificate on the reachable set.
      -- Its fundamental circuits remain reachable along backward exchange
      -- edges. The frozen BFS table must first be proved closed under edges.
      sorry

  | some p =>
    simp only
    -- BLOCKER: prove the returned path is shortest and simple, so `take n`
    -- changes nothing; toggling that path preserves both independence predicates
    -- and increases cardinality by one. The frozen layers are essential here:
    -- a merely reachable path, without shortestness, need not preserve independence.
    sorry

end CountingMatroid.Analysis.IntersectionAugmentation

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · partial · proved separator_card_le and used it in the no-path branch. The two remaining rank certificates are stated over the actual final BFS-reachable set; path exchange correctness remains open. Both live handoff waves so far were mechanically rejected.

* r15 · open · a concrete split on findPath closes preservation in the no-path branch but leaves the maximum-cardinality separator; the path branch requires shortestness, simplicity, and common-independence preservation. The first live handoff request was mechanically rejected.
-/
