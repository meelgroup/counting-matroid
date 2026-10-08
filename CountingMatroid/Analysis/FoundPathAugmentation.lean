import CountingMatroid.Analysis.IntersectionSearch
import CountingMatroid.Analysis.FindPathCertificate
import CountingMatroid.Analysis.ShortestExchangeAugmentation

set_option autoImplicit false

/-!
The successful branch of the concrete exchange search. Correctness requires
both the algorithmic fact that the selected reverse path is shortest and the
matroid fact that toggling a shortest exchange path augments independence.
The explicit ShortestCertificate separates these obligations. The parent now
composes the two child statements; both children remain open proof obligations.
The checked value bridge removes operation charges and the certified length
bound removes the cap. Arbitrary directed paths do not satisfy the conclusion.
-/

namespace CountingMatroid.Analysis.FoundPathAugmentation

open CountingMatroid.Model CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Toggling the shortest path actually returned by the capped
search preserves both matroids' independence and adds one element.
TEXLINE: main.tex:283-289 -/
theorem found_path_augmentation {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (I : Finset (Fin n)) (hI₁ : M₁.Indep (I : Set (Fin n)))
    (hI₂ : M₂.Indep (I : Set (Fin n))) (p : List (Fin n))
    (hp : (findPath (buildGraph o₁ o₂ I).val).val = some p) :
    let next := (Arlib.Computation.Charged.foldl toggle (p.take n) I).val
    M₁.Indep (next : Set (Fin n)) ∧ M₂.Indep (next : Set (Fin n)) ∧
      next.card = I.card + 1 := by
  cases n with
  | zero =>
    simp [findPath] at hp
  | succ n =>
    cases n with
    | zero =>
      classical
      let graph := (buildGraph o₁ o₂ I).val
      have hfind : (findPath graph).val =
          if (graph.terminals 0).1 && (graph.terminals 0).2 then some [0] else none := by
        cases hs : (graph.terminals 0).1 <;> cases ht : (graph.terminals 0).2 <;>
          simp [findPath, initialPaths, tabulate_val, List.finRange_succ,
            relaxPaths, relaxVertex, predecessorStep, CountingMatroid.Model.Operations.isSome,
            sinkStep, hs, ht]
      change (findPath graph).val = some p at hp
      rw [hfind] at hp
      split at hp
      · rename_i hflags
        obtain ⟨hs, ht⟩ := Bool.and_eq_true_iff.mp hflags
        have hp' : p = [0] := (Option.some.inj hp).symm
        subst p
        have hterminal : graph.terminals 0 =
            (decide ((0 : Fin 1) ∉ I ∧ M₁.Indep (insert 0 (I : Set (Fin 1)))),
             decide ((0 : Fin 1) ∉ I ∧ M₂.Indep (insert 0 (I : Set (Fin 1))))) := by
          simp only [graph, buildGraph_val]
          exact testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂ I 0
        rw [hterminal] at hs ht
        have hfirst : (0 : Fin 1) ∉ I ∧ M₁.Indep (insert 0 (I : Set (Fin 1))) := by
          simpa only [decide_eq_true_eq] using hs
        have hsecond : (0 : Fin 1) ∉ I ∧ M₂.Indep (insert 0 (I : Set (Fin 1))) := by
          simpa only [decide_eq_true_eq] using ht
        simpa [toggle, CountingMatroid.Model.Operations.containsElement,
          CountingMatroid.Model.Operations.insertElement, hfirst.1] using
          And.intro hfirst.2 (And.intro hsecond.2 (Finset.card_insert_of_notMem hfirst.1))
      · contradiction
    | succ n =>
      classical
      have hc := CountingMatroid.Analysis.FindPathCertificate.findPath_certificate
        (buildGraph o₁ o₂ I).val p hp
      have haug := CountingMatroid.Analysis.ShortestExchangeAugmentation.shortest_exchange_augmentation
        M₁ M₂ o₁ o₂ hfull h₁ h₂ I hI₁ hI₂ p hc
      dsimp only
      rw [List.take_of_length_le hc.length_le,
        CountingMatroid.Analysis.ExchangePathCertificate.toggle_fold_value]
      exact haug

end CountingMatroid.Analysis.FoundPathAugmentation

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · decomposed · preserved the n=0 and n=1 proofs; n≥2 now composes a graph-only shortest-path certificate and an implementation-independent matroid augmentation lemma. Both child obligations remain open.

* r19 · partial · proved successful augmentation for n=0 and n=1. For n≥2, unfolding frozen BFS and the closure characterization of independence leave shortestness, alternating simple-path cardinality, and closure avoidance unproved.

* r19 · open · proved the empty-ground successful branch impossible and exposed the frozen BFS/sink selection for the positive-ground branch; shortest path and circuit exchange invariants remain.
-/
