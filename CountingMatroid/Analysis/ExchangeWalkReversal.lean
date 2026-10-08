import CountingMatroid.Analysis.ExchangePathCertificate
import Mathlib.Data.List.Chain

set_option autoImplicit false

/-! Reversing an exchange graph interchanges its sources and sinks. Reverse
list paths then satisfy the same augmentation and shortestness predicates. -/
namespace CountingMatroid.Analysis.ExchangeWalkReversal
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: Reverse every edge and interchange source and sink flags. -/
def reverse_exchange_graph {n : ℕ} (g : ExchangeGraph n) : ExchangeGraph n :=
  ⟨fun v => ((g.terminals v).2, (g.terminals v).1), fun u v => g.edges v u⟩

/-- INTERNAL: SourceWalk is the ordinary adjacent-edge chain together with
its source flag at the last vertex of the reverse list. -/
theorem source_walk_iff_chain {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) :
    SourceWalk g p ↔
      p.IsChain (fun v u => g.edges u v = true) ∧
        ∃ v, p.getLast? = some v ∧ (g.terminals v).1 = true := by
  constructor
  · intro hw
    induction hw with
    | source v hs => exact ⟨by simp, v, rfl, hs⟩
    | step u v tail hw he ih =>
      exact ⟨List.isChain_cons_cons.mpr ⟨he, ih.1⟩, by
        simpa only [List.getLast?_cons_cons] using ih.2⟩
  · induction p with
    | nil => simp
    | cons v p ih =>
      cases p with
      | nil =>
        rintro ⟨_, w, heq, hs⟩
        have : v = w := Option.some.inj heq
        subst w
        exact .source v hs
      | cons u tail =>
        rintro ⟨hchain, hlast⟩
        obtain ⟨he, hchain⟩ := List.isChain_cons_cons.mp hchain
        apply SourceWalk.step u v tail
        · apply ih
          exact ⟨hchain, by simpa only [List.getLast?_cons_cons] using hlast⟩
        · exact he

/-- INTERNAL: Augmenting walks are adjacent-edge chains whose last vertex
is a source and whose first vertex is a sink. -/
theorem augmenting_walk_iff_chain {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) :
    AugmentingWalk g p ↔
      p.IsChain (fun v u => g.edges u v = true) ∧
        (∃ v, p.getLast? = some v ∧ (g.terminals v).1 = true) ∧
        (∃ v, p.head? = some v ∧ (g.terminals v).2 = true) := by
  rw [AugmentingWalk, source_walk_iff_chain]
  constructor
  · rintro ⟨⟨hchain, hlast⟩, v, tail, heq, hs⟩
    exact ⟨hchain, hlast, v, List.head?_eq_some_iff.mpr ⟨tail, heq⟩, hs⟩
  · rintro ⟨hchain, hlast, v, hhead, hs⟩
    obtain ⟨tail, heq⟩ := List.head?_eq_some_iff.mp hhead
    exact ⟨⟨hchain, hlast⟩, v, tail, heq, hs⟩

/-- INTERNAL: Reverse an augmenting walk to exchange the roles of the two
matroids in the single-matroid independence argument. -/
theorem augmenting_walk_reverse {n : ℕ} {g : ExchangeGraph n} {p : List (Fin n)}
    (hw : AugmentingWalk g p) : AugmentingWalk (reverse_exchange_graph g) p.reverse := by
  obtain ⟨hchain, hlast, hhead⟩ := (augmenting_walk_iff_chain g p).mp hw
  apply (augmenting_walk_iff_chain (reverse_exchange_graph g) p.reverse).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact List.isChain_reverse.mpr hchain
  · simpa only [List.getLast?_reverse, reverse_exchange_graph] using hhead
  · simpa only [List.head?_reverse, reverse_exchange_graph] using hlast

/-- INTERNAL: Global shortestness and simplicity survive graph and list
reversal, so the second matroid uses the same certified induction. -/
theorem shortest_certificate_reverse {n : ℕ} {g : ExchangeGraph n}
    {p : List (Fin n)} (hc : ShortestCertificate g p) :
    ShortestCertificate (reverse_exchange_graph g) p.reverse := by
  refine ⟨augmenting_walk_reverse hc.augmenting,
    List.nodup_reverse.mpr hc.simple, ?_, ?_⟩
  · simpa only [List.length_reverse] using hc.length_le
  · intro q hq
    have hrev := augmenting_walk_reverse hq
    change AugmentingWalk g q.reverse at hrev
    simpa only [List.length_reverse] using hc.minimal q.reverse hrev

end CountingMatroid.Analysis.ExchangeWalkReversal
