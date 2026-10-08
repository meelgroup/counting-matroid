import CountingMatroid.Analysis.FirstPhaseFailure
import Mathlib.Data.List.Induction

set_option autoImplicit false

namespace CountingMatroid.Analysis.DefectPartitionPositive

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: One concrete state of an ordered defect class: take x at every
pair other than the empty pair, and also y at the full pair.
TEXLINE: main.tex:712-735 -/
def defectState {n : ℕ} (index : DefectIndex n) : PairedSet n :=
  (Finset.univ.erase index.emptyPair).image (fun i => (i, false)) ∪
    {(index.fullPair, true)}

/-- INTERNAL: Occupancy of the explicit defect witness, used to evaluate the
program's classifier rather than assume a mathematical classifier.
TEXLINE: main.tex:712-735 -/
private theorem defectState_membership {n : ℕ} (index : DefectIndex n)
    (i : Fin n) :
    ((i, false) ∈ defectState index ↔ i ≠ index.emptyPair) ∧
      ((i, true) ∈ defectState index ↔ i = index.fullPair) := by
  classical
  simp [defectState]

/-- INTERNAL: A charged fold's return value is the ordinary fold of return
values. The classifier's implementation is inspected through this equality. -/
private theorem foldl_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β) (l : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f l b).val =
      l.foldl (fun acc a => (f acc a).val) b := by
  induction l generalizing b with
  | nil => rfl
  | cons a l ih =>
      simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons]
        using ih (f b a).val

/-- INTERNAL: The actual pair scan accepts the explicit ordered-defect
witness. Repeated empty/full-pair checks are controlled by the duplicate-free
enumeration, and its off-diagonal check uses the index's distinctness proof.
TEXLINE: main.tex:712-735,746-751 -/
theorem defect_state_classified {n : ℕ} (index : DefectIndex n) :
    (classifyState (defectState index)).val =
      .defect index.emptyPair index.fullPair := by
  classical
  let step : (Option (Fin n) × Option (Fin n) × Bool) → Fin n →
      Arlib.Computation.Charged Op Cell (Option (Fin n) × Option (Fin n) × Bool) :=
    fun acc i => do
      let x ← containsPaired (defectState index) (i, false)
      let y ← containsPaired (defectState index) (i, true)
      if x then
        if y then
          let seen ← isSome acc.2.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (acc.1, some i, acc.2.2)
        else pure acc
      else
        if y then pure acc
        else
          let seen ← isSome acc.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (some i, acc.2.1, acc.2.2)
  let scan := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) =>
    if i = index.emptyPair then
      if acc.1.isSome then (acc.1, acc.2.1, true)
      else (some i, acc.2.1, acc.2.2)
    else if i = index.fullPair then
      if acc.2.1.isSome then (acc.1, acc.2.1, true)
      else (acc.1, some i, acc.2.2)
    else acc
  have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
      (step acc i).val = scan acc i := by
    by_cases he : i = index.emptyPair
    · simp [step, scan, containsPaired, isSome, defectState_membership, he,
        index.distinct]
      split <;> rename_i hseen <;> simp [hseen]
    · by_cases hf : i = index.fullPair
      · simp [step, scan, containsPaired, isSome, defectState_membership, hf,
          index.distinct.symm]
        split <;> rename_i hseen <;> simp [hseen]
      · simp [step, scan, containsPaired, isSome, defectState_membership, he, hf]
  have hfold (l : List (Fin n)) (hl : l.Nodup) :
      l.foldl scan (none, none, false) =
        (if index.emptyPair ∈ l then some index.emptyPair else none,
         if index.fullPair ∈ l then some index.fullPair else none, false) := by
    induction l using List.reverseRecOn with
    | nil => simp
    | append_singleton l i ih =>
      have hnodup : (l.concat i).Nodup := by
        simpa only [List.concat_eq_append] using hl
      obtain ⟨hi, hl'⟩ := (List.nodup_concat l i).mp hnodup
      rw [List.foldl_append, ih hl', List.foldl_cons, List.foldl_nil]
      by_cases he : i = index.emptyPair
      · subst i
        simp [scan, hi, index.distinct.symm]
      · by_cases hf : i = index.fullPair
        · subst i
          simp [scan, hi, he, index.distinct]
        · simp [scan, he, hf, Ne.symm he, Ne.symm hf]
  have hscan : (Arlib.Computation.Charged.foldl step (List.finRange n)
      (none, none, false)).val = (some index.emptyPair, some index.fullPair, false) := by
    rw [foldl_value]
    simp_rw [hstep]
    simpa using hfold (List.finRange n) (List.nodup_finRange n)
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl step (List.finRange n)
      (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  simp [hscan, indexEqual, index.distinct]

/-- INTERNAL: Every ordered defect class has positive unweighted partition
sum at a positive parameter. The witness is accepted by the actual program
classifier, so this statement applies to `FirstPhaseFailure.defectPartition`.
TEXLINE: main.tex:712-735 -/
theorem defect_partition_pos {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (index : DefectIndex n) :
    0 < FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
  classical
  let term := fun state : PairedSet n =>
    if (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0
  have hnonneg : ∀ state, 0 ≤ term state := by
    intro state
    dsimp only [term]
    split_ifs
    · exact (pow_pos hq _).le
    · exact le_rfl
  have hwitness : 0 < term (defectState index) := by
    dsimp only [term]
    rw [defect_state_classified, if_pos rfl]
    exact pow_pos hq _
  exact hwitness.trans_le (Finset.single_le_sum (fun state _ => hnonneg state)
    (Finset.mem_univ (defectState index)))

end CountingMatroid.Analysis.DefectPartitionPositive
