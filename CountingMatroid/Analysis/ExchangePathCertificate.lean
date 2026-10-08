import CountingMatroid.Analysis.IntersectionSearch

set_option autoImplicit false

/-! Proof-side certificates use the search's reverse list orientation. Minimality
is over all source-to-sink walks, not just paths discovered by the implementation. -/
namespace CountingMatroid.Analysis.ExchangePathCertificate
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: A nonempty reverse walk whose last vertex is a source. -/
inductive SourceWalk {n : ℕ} (g : ExchangeGraph n) : List (Fin n) → Prop
  | source (v : Fin n) : (g.terminals v).1 = true → SourceWalk g [v]
  | step (u v : Fin n) (tail : List (Fin n)) : SourceWalk g (u :: tail) →
      g.edges u v = true → SourceWalk g (v :: u :: tail)

/-- INTERNAL: A reverse source walk ending at a sink. -/
def AugmentingWalk {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) : Prop :=
  SourceWalk g p ∧ ∃ v tail, p = v :: tail ∧ (g.terminals v).2 = true

/-- INTERNAL: Mathematical interface between the capped BFS and matroid exchange.
The length bound makes the program's final take harmless. -/
structure ShortestCertificate {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n)) : Prop where
  augmenting : AugmentingWalk g p
  simple : p.Nodup
  length_le : p.length ≤ n
  minimal : ∀ q, AugmentingWalk g q → p.length ≤ q.length

/-- INTERNAL: Forget operation charges when toggling a list of vertices. -/
theorem toggle_fold_value {n : ℕ} (p : List (Fin n)) (I : Finset (Fin n)) :
    (Arlib.Computation.Charged.foldl toggle p I).val =
      p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I := by
  classical
  induction p generalizing I with
  | nil => rfl
  | cons i p ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons]
    by_cases hi : i ∈ I <;> simpa [hi, toggle, CountingMatroid.Model.Operations.containsElement,
      CountingMatroid.Model.Operations.insertElement] using
      ih (if i ∈ I then I.erase i else insert i I)
end CountingMatroid.Analysis.ExchangePathCertificate
