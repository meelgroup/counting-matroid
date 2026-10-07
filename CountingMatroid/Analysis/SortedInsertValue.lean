import CountingMatroid.Model.Program
import Mathlib.Data.List.Sort

/-!
# Value of the charged rational insertion scan

On a sorted list, the charged scan inserts a rational at the same position as
`List.orderedInsert`. The proof first identifies the scan with strict insertion,
then uses sortedness to handle repeated values.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis

/-- INTERNAL: On sorted input, the charged insertion scan has the value of ordinary ordered insertion. -/
theorem sortedInsert_value_eq (value : ℚ) (sorted : List ℚ)
    (hsorted : sorted.Pairwise (· ≤ ·)) :
    (CountingMatroid.Program.sortedInsert value sorted).val =
      sorted.orderedInsert (· ≤ ·) value := by
  have hfront : ∀ xs : List ℚ, (∀ x ∈ xs, value ≤ x) →
      xs.orderedInsert (· < ·) value = value :: xs := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons x xs ih =>
        intro hx
        have hvx : value ≤ x := hx x (by simp)
        have hxs : ∀ y ∈ xs, value ≤ y := by
          intro y hy
          exact hx y (by simp [hy])
        by_cases hlt : value < x
        · simp [List.orderedInsert_cons, hlt]
        · have heq : value = x := le_antisymm hvx (le_of_not_gt hlt)
          subst x
          simp [List.orderedInsert_cons, ih hxs]
  have hstrict : ∀ xs : List ℚ, xs.Pairwise (· ≤ ·) →
      xs.orderedInsert (· < ·) value = xs.orderedInsert (· ≤ ·) value := by
    intro xs
    induction xs with
    | nil => intro _; rfl
    | cons x xs ih =>
        intro hx
        have htail : xs.Pairwise (· ≤ ·) := hx.of_cons
        have hhead : ∀ y ∈ xs, x ≤ y := by
          intro y hy
          exact (List.pairwise_cons.mp hx).1 y hy
        by_cases hlt : value < x
        · simp [List.orderedInsert_cons, hlt, le_of_lt hlt]
        · by_cases heq : value = x
          · subst x
            simp [List.orderedInsert_cons, hfront xs hhead]
          · have hgt : x < value := lt_of_le_of_ne (le_of_not_gt hlt) (Ne.symm heq)
            simp [List.orderedInsert_cons, hlt, not_le_of_gt hgt, ih htail]
  let step : List ℚ × Bool → ℚ → List ℚ × Bool := fun acc item =>
    if acc.2 then (item :: acc.1, true)
    else if value < item then (item :: value :: acc.1, true)
    else (item :: acc.1, false)
  let cstep : List ℚ × Bool → ℚ →
      Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell (List ℚ × Bool) := fun acc item => do
    if acc.2 then
      let reversed ← CountingMatroid.Model.Operations.consRational item acc.1
      pure (reversed, true)
    else
      let before ← CountingMatroid.Model.Operations.ratLess value item
      if before then
        let reversed ← CountingMatroid.Model.Operations.consRational value acc.1
        let reversed ← CountingMatroid.Model.Operations.consRational item reversed
        pure (reversed, true)
      else
        let reversed ← CountingMatroid.Model.Operations.consRational item acc.1
        pure (reversed, false)
  have hstep (acc : List ℚ × Bool) (item : ℚ) :
      (cstep acc item).val = step acc item := by
    rcases acc with ⟨rev, flag⟩
    cases flag <;> simp [cstep, step, CountingMatroid.Model.Operations.ratLess,
      CountingMatroid.Model.Operations.consRational]
    split_ifs <;> simp
  have hfold : ∀ (xs : List ℚ) (acc : List ℚ × Bool),
      (Arlib.Computation.Charged.foldl cstep xs acc).val = xs.foldl step acc := by
    intro xs
    induction xs with
    | nil => intro acc; rfl
    | cons item xs ih =>
        intro acc
        simp only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons]
        rw [ih, hstep]
  have hscan : ∀ (xs rev : List ℚ) (flag : Bool),
      let result := xs.foldl step (rev, flag)
      (if result.2 then result.1.reverse else (value :: result.1).reverse) =
        rev.reverse ++ (if flag then xs else xs.orderedInsert (· < ·) value) := by
    intro xs
    induction xs with
    | nil =>
        intro rev flag
        cases flag <;> simp [step]
    | cons item xs ih =>
        intro rev flag
        cases flag with
        | true =>
            simpa [step, List.foldl_cons, List.reverse_cons, List.append_assoc] using
              ih (item :: rev) true
        | false =>
            by_cases hlt : value < item
            · simpa [step, hlt, List.foldl_cons, List.orderedInsert_cons,
                List.reverse_cons, List.append_assoc] using
                ih (item :: value :: rev) true
            · simpa [step, hlt, List.foldl_cons, List.orderedInsert_cons,
                List.reverse_cons, List.append_assoc] using
                ih (item :: rev) false
  let result := sorted.foldl step ([], false)
  have hcharged : (CountingMatroid.Program.sortedInsert value sorted).val =
      if result.2 then result.1.reverse else (value :: result.1).reverse := by
    unfold CountingMatroid.Program.sortedInsert
    change (do
      let (reversed, inserted) ← Arlib.Computation.Charged.foldl cstep sorted ([], false)
      let reversed ← if inserted then pure reversed
        else CountingMatroid.Model.Operations.consRational value reversed
      CountingMatroid.Model.Operations.reverseRationals reversed).val = _
    simp [hfold, result, CountingMatroid.Model.Operations.consRational,
      CountingMatroid.Model.Operations.reverseRationals]
    split_ifs <;> simp
  rw [hcharged]
  have hresult := hscan sorted [] false
  simpa [result, hstrict sorted hsorted] using hresult

end CountingMatroid.Analysis

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · repaired · restricted the insertion equality to sorted lists; an arbitrary unsorted input need not agree with ordered insertion at repeated values.
-/
