import CountingMatroid.Analysis.IntersectionSearch
import CountingMatroid.Analysis.ExchangeClosedBasis
import CountingMatroid.Analysis.NoPathSeparator
import CountingMatroid.Analysis.FoundPathAugmentation

set_option autoImplicit false

/-!
The augmentation-progress proof combines exact exchange-query predicates,
a graph separator when search fails, and shortest-path exchange preservation
when search succeeds. The matroid basis certificates on both sides of the
separator are proved here using `ExchangeClosedBasis`. Graph-search saturation
is proved in `NoPathSeparator`; successful-path preservation remains an
explicit obligation in `FoundPathAugmentation`. This is an internal refinement
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
  classical
  dsimp only
  unfold augmentOnce
  simp only [Arlib.Computation.Charged.val_bind]
  cases hp : (findPath (buildGraph o₁ o₂ I).val).val with
  | none =>
    simp only [Arlib.Computation.Charged.val_pure]
    refine ⟨hI₁, hI₂, Or.inr ⟨trivial, ?_⟩⟩
    intro J hJ₁ hJ₂
    let graph := (buildGraph o₁ o₂ I).val
    obtain ⟨R, hsource, hedge, hsink⟩ :=
      NoPathSeparator.no_path_separator graph hp
    have hsources (e : Fin n) : (graph.terminals e).1 = true ↔
        e ∉ I ∧ M₁.Indep (insert e (I : Set (Fin n))) := by
      simp only [graph, buildGraph_val, testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂,
        decide_eq_true_eq]
    have hsinks (e : Fin n) : (graph.terminals e).2 = true ↔
        e ∉ I ∧ M₂.Indep (insert e (I : Set (Fin n))) := by
      simp only [graph, buildGraph_val, testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂,
        decide_eq_true_eq]
    have harcs (u v : Fin n) : graph.edges u v = true ↔
        (u ∈ I ∧ v ∉ I ∧ M₁.Indep
          (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) ∨
        (u ∉ I ∧ v ∈ I ∧ M₂.Indep
          (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))) := by
      simp only [graph, buildGraph_val, testEdge_val M₁ M₂ o₁ o₂ h₁ h₂,
        decide_eq_true_eq]
    refine separator_card_le M₁ M₂ I R ?_ ?_ J hJ₁ hJ₂
    · have hb := ExchangeClosedBasis.exchange_closed_basis M₁
        (I : Set (Fin n)) (Set.univ \ (R : Set (Fin n))) hI₁
        (by rw [hfull.1]; exact Set.subset_univ _) ?_ ?_
      · simpa only [Finset.coe_sdiff, Finset.coe_univ,
          ← Set.inter_sdiff_assoc, Set.inter_univ] using hb
      · intro e he heI hind
        exact he.2 (hsource e ((hsources e).mpr ⟨heI, hind⟩))
      · intro e he heI u hu hind
        refine ⟨Set.mem_univ u, ?_⟩
        intro huR
        apply he.2
        apply hedge u e huR
        apply (harcs u e).mpr
        exact Or.inl ⟨hu, heI, by simpa only [Finset.coe_erase] using hind⟩
    · have hb := ExchangeClosedBasis.exchange_closed_basis M₂
        (I : Set (Fin n)) (R : Set (Fin n)) hI₂
        (by rw [hfull.2]; exact Set.subset_univ _) ?_ ?_
      · simpa only [Finset.coe_inter] using hb
      · intro e he heI hind
        have ht := (hsinks e).mpr ⟨heI, hind⟩
        rw [hsink e he] at ht
        contradiction
      · intro e he heI u hu hind
        apply hedge e u he
        apply (harcs e u).mpr
        exact Or.inr ⟨heI, hu, by simpa only [Finset.coe_erase] using hind⟩
  | some p =>
    obtain ⟨hnext₁, hnext₂, hcard⟩ :=
      FoundPathAugmentation.found_path_augmentation M₁ M₂ o₁ o₂ hfull h₁ h₂ I hI₁ hI₂ p hp
    exact ⟨hnext₁, hnext₂, Or.inl hcard⟩

end CountingMatroid.Analysis.IntersectionAugmentation

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · handoff rejected · both the separator/path wave and the later successful-path-only wave were mechanically rejected; all child files remain locally owned. The only remaining proof debt is found_path_augmentation for n≥2.

* r19 · partial · completed the no-path branch: proved the concrete BFS separator, finite saturation, sink exclusion, and both complementary matroid basis certificates. Successful-path preservation remains open.

* r19 · decomposed · proved both complementary matroid basis certificates using fundamental circuits; augmentation_progress elaborates through the independent no-path graph separator and successful-path preservation obligations.

* r17 · partial · proved separator_card_le and used it in the no-path branch. The two remaining rank certificates are stated over the actual final BFS-reachable set; path exchange correctness remains open. Both live handoff waves so far were mechanically rejected.

* r15 · open · a concrete split on findPath closes preservation in the no-path branch but leaves the maximum-cardinality separator; the path branch requires shortestness, simplicity, and common-independence preservation. The first live handoff request was mechanically rejected.
-/
