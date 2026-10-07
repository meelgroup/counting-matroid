import CountingMatroid.Model.Subroutines

set_option autoImplicit false

namespace CountingMatroid.Analysis.TransversalProjection

open CountingMatroid.Model

/-- INTERNAL: The concrete paired scan selects the same index set twice on a
transversal, and counts its complementary y elements.
TEXLINE: main.tex:270-280,1333-1346 -/
theorem pairedProjections_transversal {n : ℕ} (A : Finset (Fin n)) :
    (CountingMatroid.Model.Subroutines.pairedProjections
      (Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A))))).val =
      (A, A, n - A.card) := by
  classical
  let state : PairedSet n := Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A)))
  let step : (Finset (Fin n) × Finset (Fin n) × ℕ) → Fin n →
      Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell
        (Finset (Fin n) × Finset (Fin n) × ℕ) := fun acc i => do
    let inX ← CountingMatroid.Model.Operations.containsPaired state (i, false)
    let x ← if inX then CountingMatroid.Model.Operations.insertElement acc.1 i else pure acc.1
    let inY ← CountingMatroid.Model.Operations.containsPaired state (i, true)
    if inY then
      let ysize ← CountingMatroid.Model.Operations.successor acc.2.2
      pure (x, acc.2.1, ysize)
    else
      let complementY ← CountingMatroid.Model.Operations.insertElement acc.2.1 i
      pure (x, complementY, acc.2.2)
  have hstep (x y : Finset (Fin n)) (k : ℕ) (i : Fin n) :
      (step (x, y, k) i).val =
        if i ∈ A then (insert i x, insert i y, k) else (x, y, k + 1) := by
    by_cases h : i ∈ A
    · simp [step, state, CountingMatroid.Model.Operations.containsPaired,
        CountingMatroid.Model.Operations.insertElement,
        CountingMatroid.Model.Operations.successor, h]
    · simp [step, state, CountingMatroid.Model.Operations.containsPaired,
        CountingMatroid.Model.Operations.insertElement,
        CountingMatroid.Model.Operations.successor, h]
  have hfold (l : List (Fin n)) (x y : Finset (Fin n)) (k : ℕ) :
      (Arlib.Computation.Charged.foldl step l (x, y, k)).val =
      (x ∪ (l.filter (fun i => i ∈ A)).toFinset,
       y ∪ (l.filter (fun i => i ∈ A)).toFinset,
       k + (l.filter (fun i => i ∉ A)).length) := by
    induction l generalizing x y k with
    | nil => simp
    | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, hstep]
      by_cases h : i ∈ A
      · simp [h, ih, Finset.union_insert, Finset.insert_union]
      · simp [h, ih, Nat.add_assoc, Nat.add_comm]
  change (Arlib.Computation.Charged.foldl step (List.finRange n)
    ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)).val = _
  rw [hfold]
  have hfilter : (List.filter (fun i => i ∈ A) (List.finRange n)).toFinset = A := by
    ext i
    simp
  have hlen : (List.filter (fun i => i ∈ A) (List.finRange n)).length = A.card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter (fun i => i ∈ A)), hfilter]
  have htotal := List.length_eq_length_filter_add
    (l := List.finRange n) (f := fun i : Fin n => decide (i ∈ A))
  have hnot : (List.filter (fun i => !decide (i ∈ A)) (List.finRange n)).length = n - A.card := by
    have h : n = (List.filter (fun i => i ∈ A) (List.finRange n)).length +
        (List.filter (fun i => !decide (i ∈ A)) (List.finRange n)).length := by
      simpa using htotal
    omega
  simp [hfilter, hnot]

end CountingMatroid.Analysis.TransversalProjection
