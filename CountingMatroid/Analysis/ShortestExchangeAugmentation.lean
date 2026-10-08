import CountingMatroid.Analysis.ExchangePathCertificate

set_option autoImplicit false

/-! Mathematical half of augmentation: this file does not mention findPath or
its BFS tables. Global shortestness rules out the shortcuts needed in the
simultaneous-exchange argument. The theorem is still a proof obligation. -/
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: A shortest exchange-graph path augments both independent sets.
This isolates the matroid argument from the executable search and its charges.
TEXLINE: main.tex:283-289 -/
theorem shortest_exchange_augmentation {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) (p : List (Fin n))
    (hc : ShortestCertificate (buildGraph o₁ o₂ I).val p) :
    let next := p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      next.card = I.card + 1 := by
  classical
  cases hw : hc.augmenting.1 with
  | source v hs =>
    obtain ⟨w, tail, heq, ht⟩ := hc.augmenting.2
    have hwv : w = v := by simpa using (List.cons.inj heq).1.symm
    subst w
    have hterminal := testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂ I v
    have hs' : v ∉ I ∧ M₁.Indep (insert v (I : Set (Fin n))) := by
      simpa only [buildGraph_val, hterminal, decide_eq_true_eq] using hs
    have ht' : v ∉ I ∧ M₂.Indep (insert v (I : Set (Fin n))) := by
      simpa only [buildGraph_val, hterminal, decide_eq_true_eq] using ht
    simpa [hs'.1] using
      And.intro hs'.2 (And.intro ht'.2 (Finset.card_insert_of_notMem hs'.1))
  | step u v tail hwalk hedge =>
    -- Route 2: induction on source walks closes singleton augmentation,
    -- but prefixes need not end at sinks, so augmenting every prefix is
    -- not an induction invariant. Global minimality must instead control
    -- circuits introduced by simultaneous exchanges.
    dsimp only
    refine ⟨?_, ?_, ?_⟩
    · apply Matroid.indep_iff_forall_notMem_closure_sdiff'.mpr
      refine ⟨?_, ?_⟩
      · rw [hfull.1]
        exact Set.subset_univ _
      · intro e he
        -- Route 1: exact edge specifications and hc.minimal must imply
        -- closure avoidance after simultaneous exchanges, not just one edge.
        sorry
    · apply Matroid.indep_iff_forall_notMem_closure_sdiff'.mpr
      refine ⟨?_, ?_⟩
      · rw [hfull.2]
        exact Set.subset_univ _
      · intro e he
        sorry
    · -- SourceWalk plus exact edges gives alternating membership. Simplicity
      -- then prevents double toggles, and the two outside endpoints give +1.
      sorry

end CountingMatroid.Analysis.ShortestExchangeAugmentation

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · partial · proved singleton source-to-sink augmentation; prefix induction cannot reuse the sink endpoint hypothesis.

* recovery · open · closure characterization discharges both ground clauses; shortestness-to-simultaneous-exchange and alternating-cardinality arguments remain.
-/
