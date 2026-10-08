import CountingMatroid.Analysis.ExchangePathCertificate

set_option autoImplicit false

/-! Algorithmic half of successful augmentation, independent of matroid axioms.
The final sink fold has a proved length bound for arbitrary tables. The
outstanding invariant must relate each frozen BFS table entry to minimum
source-walk length; list truncation cannot be assumed to preserve a source walk. -/
namespace CountingMatroid.Analysis.FindPathCertificate
open CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: The concrete frozen-layer search returns a shortest simple
source-to-sink reverse walk, so neither list cap discards a vertex.
TEXLINE: main.tex:283-289 -/
theorem findPath_certificate {n : ℕ} (g : ExchangeGraph n) (p : List (Fin n))
    (hp : (findPath g).val = some p) : ShortestCertificate g p := by
  have hstep (paths : Paths n) (best : Option (List (Fin n))) (i : Fin n)
      (hb : ∀ q, best = some q → q.length ≤ n) :
      ∀ q, (sinkStep g paths best i).val = some q → q.length ≤ n := by
    intro q hq
    cases ht : (g.terminals i).2 <;> cases hv : paths i <;> cases best <;>
      simp [sinkStep, ht, hv, CountingMatroid.Model.Operations.lessThan] at hq hb
    all_goals first
      | (subst q; exact hb)
      | (subst q; simp only [List.length_take]; exact Nat.min_le_left _ _)
      | (split at hq <;> simp only [Arlib.Computation.Charged.val_pure,
          Option.some.injEq] at hq <;> subst q
         · simp only [List.length_take]; exact Nat.min_le_left _ _
         · exact hb)
  have hfold (paths : Paths n) (indices : List (Fin n))
      (best : Option (List (Fin n)))
      (hb : ∀ q, best = some q → q.length ≤ n) :
      ∀ q, (Arlib.Computation.Charged.foldl (sinkStep g paths) indices best).val =
        some q → q.length ≤ n := by
    induction indices generalizing best with
    | nil => exact hb
    | cons i indices ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih _ (hstep paths best i hb)
  have hlength : p.length ≤ n := by
    unfold findPath at hp
    simp only [Arlib.Computation.Charged.val_bind] at hp
    exact hfold _ _ none (by simp) p hp
  -- Route 1 exposed the two operational folds. Route 2 establishes the
  -- final sink-fold length invariant independently, even for arbitrary
  -- path tables. This does NOT justify truncating a source walk: the BFS
  -- invariant still must prove simplicity and minimality before the cap.
  refine ⟨?_, ?_, hlength, ?_⟩
  · sorry
  · sorry
  · sorry

end CountingMatroid.Analysis.FindPathCertificate

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · partial · proved final sink-fold length bound even for arbitrary path tables; source-to-sink validity, simplicity and global minimality remain.

* recovery · open · exposed both folds; the bounded-distance frozen-table invariant and final minimum-sink selection remain.
-/
