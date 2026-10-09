import CountingMatroid.Analysis.ClassifiedStateSelection
import Mathlib.Data.List.Nodup
import Mathlib.Data.List.Induction

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The charged selector enumerates the occupied and unoccupied labels
without repetition, in the program's fixed x/y order. -/
namespace CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: The complete ordered paired-label list visited by selection. -/
def pairedLabels (n : ℕ) : List (PairedGround n) :=
  (List.finRange n).flatMap (fun i => [(i, false), (i, true)])

/-- INTERNAL: Each paired label occurs in the program's enumeration. -/
theorem mem_pairedLabels {n : ℕ} (a : PairedGround n) : a ∈ pairedLabels n := by
  rcases a with ⟨i, b⟩
  cases b <;> simp [pairedLabels, List.mem_flatMap]

/-- INTERNAL: The complete paired-label enumeration contains no duplicates. -/
theorem pairedLabels_nodup (n : ℕ) : (pairedLabels n).Nodup := by
  have h := (List.nodup_finRange n).product
    (show ([false, true] : List Bool).Nodup by decide)
  simpa [pairedLabels, List.product, SProd.sprod] using h

/-- INTERNAL: Eligible labels in exactly the order of the charged scan. -/
def selectedLabels {n : ℕ} (state : PairedSet n) (occupied : Bool) :
    List (PairedGround n) :=
  (pairedLabels n).filter (fun a => decide (decide (a ∈ state) = occupied))

/-- INTERNAL: The selection list denotes the requested occupied/complement set. -/
theorem selectedLabels_toFinset {n : ℕ} (state : PairedSet n) (occupied : Bool) :
    (selectedLabels state occupied).toFinset = if occupied then state else stateᶜ := by
  classical
  ext a
  cases occupied <;> simp [selectedLabels, mem_pairedLabels]

/-- INTERNAL: The eligible labels also contain no duplicates. -/
theorem selectedLabels_nodup {n : ℕ} (state : PairedSet n) (occupied : Bool) :
    (selectedLabels state occupied).Nodup :=
  (pairedLabels_nodup n).filter _

/-- INTERNAL: Both selection lists have n entries on an n-element paired state. -/
theorem selectedLabels_length {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) : (selectedLabels state occupied).length = n := by
  have h := List.toFinset_card_of_nodup (selectedLabels_nodup state occupied)
  rw [selectedLabels_toFinset] at h
  cases occupied <;> simp [hcard, Finset.card_compl, PairedGround] at h <;> omega

/-- INTERNAL: Split a charged selector fold at a deterministic list boundary. -/
private theorem selection_fold_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell β)
    (xs ys : List α) (acc : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) acc).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs acc).val).val := by
  induction xs generalizing acc with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f acc x).val

/-- INTERNAL: One selection visit increments its eligible counter and records
only the unique matching position. -/
private theorem selection_visit_value {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) (acc : Option (PairedGround n) × ℕ)
    (a : PairedGround n) :
    (selectionVisit state occupied k acc a).val =
      if decide (a ∈ state) = occupied then
        (if acc.2 = k then some a else acc.1, acc.2 + 1) else acc := by
  cases occupied <;> by_cases ha : a ∈ state <;> by_cases hk : acc.2 = k <;>
    simp [selectionVisit, Model.Operations.containsPaired,
      Model.Operations.natEqual, Model.Operations.successor, ha, hk]

/-- INTERNAL: The charged scan is exactly indexed lookup in the filtered list. -/
private theorem selection_fold_lookup {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) (xs : List (PairedGround n)) :
    (Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
      xs (none, 0)).val =
    ((xs.filter (fun a => decide (decide (a ∈ state) = occupied)))[k]?,
      (xs.filter (fun a => decide (decide (a ∈ state) = occupied))).length) := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs a ih =>
      rw [selection_fold_append, ih]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil, selection_visit_value,
        List.filter_append, List.filter_cons, List.filter_nil]
      by_cases ha : decide (a ∈ state) = occupied
      · simp only [ha, decide_true, ite_true, List.length_append,
          List.length_cons, List.length_nil, Nat.add_zero]
        congr 1
        rw [List.getElem?_append]
        by_cases hk : k < (xs.filter (fun a => decide (decide (a ∈ state) = occupied))).length
        · rw [if_pos hk, if_neg (by omega)]
        · rw [if_neg hk]
          by_cases heq : (xs.filter (fun a => decide (decide (a ∈ state) = occupied))).length = k
          · simp [heq]
          · rw [if_neg heq, List.getElem?_eq_none (by omega),
              List.getElem?_eq_none (by simp; omega)]
      · simp [ha]

/-- INTERNAL: Flattening the two visits per index preserves the charged scan. -/
private theorem selection_fold_flatten {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) (xs : List (Fin n))
    (acc : Option (PairedGround n) × ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc i =>
      Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
        [(i, false), (i, true)] acc) xs acc).val =
    (Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
      (xs.flatMap (fun i => [(i, false), (i, true)])) acc).val := by
  induction xs generalizing acc with
  | nil => rfl
  | cons i xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, ih, List.flatMap_cons,
        selection_fold_append]

/-- INTERNAL: Actual program lookup equals lookup in its ordered eligible list. -/
theorem select_paired_list {n : ℕ} (state : PairedSet n) (occupied : Bool) (k : ℕ) :
    (selectPaired state occupied k).val = (selectedLabels state occupied)[k]? := by
  simp only [selectPaired, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, selection_fold_flatten]
  rw [selection_fold_lookup]
  rfl

/-- INTERNAL: Select a label as an element of the actual occupied/complement set. -/
def selectedLabel {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) (k : Fin n) :
    {a : PairedGround n // a ∈ if occupied then state else stateᶜ} :=
  ⟨(selectedLabels state occupied)[k.val]'(by rw [selectedLabels_length state occupied hcard]; exact k.isLt),
    by
      have h := List.getElem_mem
        (show k.val < (selectedLabels state occupied).length by
          rw [selectedLabels_length state occupied hcard]; exact k.isLt)
      rw [← selectedLabels_toFinset state occupied]
      exact List.mem_toFinset.mpr h⟩

/-- INTERNAL: The selectedLabel map agrees with the executable selection result. -/
theorem select_paired_selectedLabel {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (hcard : state.card = n) (k : Fin n) :
    (selectPaired state occupied k.val).val = some (selectedLabel state occupied hcard k).val := by
  rw [select_paired_list]
  exact List.getElem?_eq_getElem (by rw [selectedLabels_length state occupied hcard]; exact k.isLt)

/-- INTERNAL: Uniform in-range selection indices bijectively enumerate the
occupied or unoccupied labels, including n=1.
TEXLINE: main.tex:746-751 -/
theorem select_paired_bijective {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) : Function.Bijective (selectedLabel state occupied hcard) := by
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  constructor
  · intro i j hij
    apply Fin.ext
    have hval := congrArg Subtype.val hij
    exact (selectedLabels_nodup state occupied).getElem_inj_iff.mp hval
  · simp only [Fintype.card_fin, Fintype.card_coe]
    cases occupied <;> simp [Finset.card_compl, hcard, PairedGround] <;> omega

/-- INTERNAL: Transport a finite uniform index sum to the requested label set. -/
theorem select_paired_sum {n : ℕ} (state : PairedSet n) (occupied : Bool)
    (hcard : state.card = n) (F : PairedGround n → ℝ) :
    (∑ k : Fin n, F (selectedLabel state occupied hcard k).val) =
      ∑ a ∈ (if occupied then state else stateᶜ), F a := by
  classical
  have h := Fintype.sum_bijective (selectedLabel state occupied hcard)
    (select_paired_bijective state occupied hcard)
    (fun k => F (selectedLabel state occupied hcard k).val) (fun a => F a.val)
    (fun _ => rfl)
  simpa only [Finset.sum_coe_sort] using h

end CountingMatroid.Analysis.SelectedPairedBijection
