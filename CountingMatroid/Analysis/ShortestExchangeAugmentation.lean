import CountingMatroid.Analysis.ExchangePathCertificate
import CountingMatroid.Analysis.ExchangeWalkCardinality
import CountingMatroid.Analysis.ShortestSourceWalkIndependence
import CountingMatroid.Analysis.ExchangeWalkReversal

set_option autoImplicit false

/-! Mathematical half of augmentation: this file does not mention findPath or
its BFS tables. Global shortestness rules out the shortcuts needed in the
simultaneous-exchange argument. Fundamental-circuit induction establishes
independence for the first matroid, graph reversal establishes it for the second,
and alternating membership establishes the cardinality increment. -/
namespace CountingMatroid.Analysis.ShortestExchangeAugmentation
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate
open CountingMatroid.Analysis.ShortestSourceWalkIndependence
open CountingMatroid.Analysis.ExchangeWalkReversal
open scoped symmDiff

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
  have ht (v : Fin n) :
      ((buildGraph o₁ o₂ I).val.terminals v).1 = true ↔
        v ∉ I ∧ M₁.Indep (insert v (I : Set (Fin n))) := by
    simp only [buildGraph_val, testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂,
      decide_eq_true_eq]
  have he (u v : Fin n) : (buildGraph o₁ o₂ I).val.edges u v = true ↔
      (u ∈ I ∧ v ∉ I ∧ M₁.Indep (insert v (↑(I.erase u) : Set (Fin n)))) ∨
      (u ∉ I ∧ v ∈ I ∧ M₂.Indep (insert u (↑(I.erase v) : Set (Fin n)))) := by
    simp only [buildGraph_val, testEdge_val M₁ M₂ o₁ o₂ h₁ h₂,
      decide_eq_true_eq]
  have halt (u v : Fin n) (huv : (buildGraph o₁ o₂ I).val.edges u v = true) :
      (u ∈ I ∧ v ∉ I) ∨ (u ∉ I ∧ v ∈ I) := by
    rcases (he u v).mp huv with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
    · exact Or.inl ⟨hu, hv⟩
    · exact Or.inr ⟨hu, hv⟩
  have hexch (u v : Fin n) (hu : u ∈ I) (hv : v ∉ I) :
      (buildGraph o₁ o₂ I).val.edges u v = true ↔
        M₁.Indep (insert v (↑(I.erase u) : Set (Fin n))) := by
    rw [he]
    simp only [hu, hv, not_true_eq_false, not_false_eq_true, true_and,
      false_and, or_false]
  have hmin : ∀ v tail, p = v :: tail → ∀ q,
      SourceWalk (buildGraph o₁ o₂ I).val (v :: q) →
      p.length ≤ (v :: q).length := by
    intro v tail hp q hq
    obtain ⟨w, rest, heq, hsink⟩ := hc.augmenting.2
    have hvw := (List.cons.inj (hp.symm.trans heq)).1
    subst w
    exact hc.minimal (v :: q) ⟨hq, v, q, rfl, hsink⟩
  dsimp only
  rw [toggle_fold_symmDiff I p hc.simple]
  refine ⟨?_, ?_, ?_⟩
  · exact (shortest_source_walk_independence M₁ (buildGraph o₁ o₂ I).val I
      hfull.1 hI₁ ht halt hexch p hc.augmenting.1 hc.simple hmin).1
  · have hc' := shortest_certificate_reverse hc
    have ht' (v : Fin n) :
        ((reverse_exchange_graph (buildGraph o₁ o₂ I).val).terminals v).1 = true ↔
          v ∉ I ∧ M₂.Indep (insert v (I : Set (Fin n))) := by
      simp only [reverse_exchange_graph, buildGraph_val,
        testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂, decide_eq_true_eq]
    have halt' (u v : Fin n)
        (huv : (reverse_exchange_graph (buildGraph o₁ o₂ I).val).edges u v = true) :
        (u ∈ I ∧ v ∉ I) ∨ (u ∉ I ∧ v ∈ I) := by
      rcases halt v u huv with ⟨hv, hu⟩ | ⟨hv, hu⟩
      · exact Or.inr ⟨hu, hv⟩
      · exact Or.inl ⟨hu, hv⟩
    have hexch' (u v : Fin n) (hu : u ∈ I) (hv : v ∉ I) :
        (reverse_exchange_graph (buildGraph o₁ o₂ I).val).edges u v = true ↔
          M₂.Indep (insert v (↑(I.erase u) : Set (Fin n))) := by
      change (buildGraph o₁ o₂ I).val.edges v u = true ↔ _
      rw [he]
      simp only [hu, hv, not_true_eq_false, not_false_eq_true, true_and,
        false_and, false_or]
    have hmin' : ∀ v tail, p.reverse = v :: tail → ∀ q,
        SourceWalk (reverse_exchange_graph (buildGraph o₁ o₂ I).val) (v :: q) →
        p.reverse.length ≤ (v :: q).length := by
      intro v tail hp q hq
      obtain ⟨w, rest, heq, hsink⟩ := hc'.augmenting.2
      have hvw := (List.cons.inj (hp.symm.trans heq)).1
      subst w
      exact hc'.minimal (v :: q) ⟨hq, v, q, rfl, hsink⟩
    simpa only [List.toFinset_reverse] using
      (shortest_source_walk_independence M₂
        (reverse_exchange_graph (buildGraph o₁ o₂ I).val) I hfull.2 hI₂
        ht' halt' hexch' p.reverse hc'.augmenting.1 hc'.simple hmin').1
  · simpa only [toggle_fold_symmDiff I p hc.simple] using
      CountingMatroid.Analysis.ExchangeWalkCardinality.augmenting_walk_cardinality
        M₁ M₂ o₁ o₂ h₁ h₂ I p hc.augmenting hc.simple

end CountingMatroid.Analysis.ShortestExchangeAugmentation

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · closed shortest_exchange_augmentation with fundamental-circuit induction, reversed shortest walks, and alternating-toggle cardinality; all three supporting modules are proved.

* recovery · partial · proved singleton source-to-sink augmentation; prefix induction cannot reuse the sink endpoint hypothesis.

* recovery · open · closure characterization discharges both ground clauses; shortestness-to-simultaneous-exchange and alternating-cardinality arguments remain.
-/
