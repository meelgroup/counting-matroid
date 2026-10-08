import CountingMatroid.Analysis.FirstPhaseFailure
import CountingMatroid.Analysis.BoundedRunPhaseHistory
import Mathlib.Data.List.Induction

set_option autoImplicit false

namespace CountingMatroid.Analysis.InitialMultipliersGood

open CountingMatroid.Model CountingMatroid.Analysis
open CountingMatroid.Program CountingMatroid.Model.Operations

/-- INTERNAL: The return value of one pair-classification visit. -/
private def scanPair {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    Option (Fin n) × Option (Fin n) × Bool :=
  if (i, false) ∈ state then
    if (i, true) ∈ state then
      if acc.2.1.isSome then (acc.1, acc.2.1, true)
      else (acc.1, some i, acc.2.2)
    else acc
  else if (i, true) ∈ state then acc
  else if acc.1.isSome then (acc.1, acc.2.1, true)
  else (some i, acc.2.1, acc.2.2)

/-- INTERNAL: The charged pair-classification visit, identical to the
anonymous visit used by `Program.classifyState`. -/
private def classifierVisit {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    Arlib.Computation.Charged Op Cell (Option (Fin n) × Option (Fin n) × Bool) := do
  let x ← containsPaired state (i, false)
  let y ← containsPaired state (i, true)
  if x then
    if y then
      let seen ← isSome acc.2.1
      if seen then pure (acc.1, acc.2.1, true)
      else pure (acc.1, some i, acc.2.2)
    else pure acc
  else if y then pure acc
  else
    let seen ← isSome acc.1
    if seen then pure (acc.1, acc.2.1, true)
    else pure (some i, acc.2.1, acc.2.2)

/-- INTERNAL: Evaluate one charged visit, preserving all duplicate flags. -/
private theorem classifier_visit_value {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
    (classifierVisit state acc i).val = scanPair state acc i := by
  rcases acc with ⟨empty, full, flag⟩
  by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
    cases empty <;> cases full <;>
    simp [classifierVisit, scanPair, containsPaired, isSome, hx, hy]

/-- INTERNAL: Evaluate a classifier fold as the ordinary fold of its
per-pair return values. -/
private theorem classifier_fold_value {n : ℕ} (state : PairedSet n)
    (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
    (Arlib.Computation.Charged.foldl (classifierVisit state) l acc).val =
      l.foldl (scanPair state) acc := by
  induction l generalizing acc with
  | nil => rfl
  | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, classifier_visit_value,
        List.foldl_cons, ih]

/-- INTERNAL: Evaluate the final classifier decision after its pair scan.
The last off-diagonal check is retained as ordinary index equality. -/
private theorem classify_value {n : ℕ} (state : PairedSet n) :
    let result := (List.finRange n).foldl (scanPair state) (none, none, false)
    (classifyState state).val =
      if result.2.2 then .invalid else
        match result.1, result.2.1 with
        | none, none => .transversal
        | some i, some j => if i = j then .invalid else .defect i j
        | _, _ => .invalid := by
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl (classifierVisit state)
      (List.finRange n) (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  rw [Arlib.Computation.Charged.val_bind, classifier_fold_value]
  generalize (List.finRange n).foldl (scanPair state) (none, none, false) = result
  rcases result with ⟨empty, full, flag⟩
  cases flag <;> cases empty <;> cases full <;> simp [indexEqual, apply_ite]


/-- INTERNAL: A classifier visit with a false duplicate flag retains every
previously recorded hole/full pair, and records precisely this visit's pair. -/
private theorem scan_pair_false {n : ℕ} (state : PairedSet n)
    (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n)
    (hflag : (scanPair state acc i).2.2 = false) :
    acc.2.2 = false ∧
    (∀ k, (scanPair state acc i).1 = some k ↔ acc.1 = some k ∨
      (i = k ∧ (i, false) ∉ state ∧ (i, true) ∉ state)) ∧
    (∀ k, (scanPair state acc i).2.1 = some k ↔ acc.2.1 = some k ∨
      (i = k ∧ (i, false) ∈ state ∧ (i, true) ∈ state)) := by
  rcases acc with ⟨empty, full, flag⟩
  by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
    cases empty <;> cases full <;> cases flag <;>
    simp_all [scanPair]

/-- INTERNAL: If the final duplicate flag is false, the two recorded indices
are exactly the empty/full pairs visited by the classifier fold. -/
private theorem scan_fold_false {n : ℕ} (state : PairedSet n)
    (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool)
    (hflag : (l.foldl (scanPair state) acc).2.2 = false) :
    acc.2.2 = false ∧
    (∀ k, (l.foldl (scanPair state) acc).1 = some k ↔ acc.1 = some k ∨
      (k ∈ l ∧ (k, false) ∉ state ∧ (k, true) ∉ state)) ∧
    (∀ k, (l.foldl (scanPair state) acc).2.1 = some k ↔ acc.2.1 = some k ∨
      (k ∈ l ∧ (k, false) ∈ state ∧ (k, true) ∈ state)) := by
  induction l generalizing acc with
  | nil => simpa using hflag
  | cons i l ih =>
    obtain ⟨hstep, he, hf⟩ := ih (scanPair state acc i) hflag
    obtain ⟨hacc, hse, hsf⟩ := scan_pair_false state acc i hstep
    refine ⟨hacc, ?_, ?_⟩
    · intro k
      rw [List.foldl_cons, he, hse, List.mem_cons]
      aesop
    · intro k
      rw [List.foldl_cons, hf, hsf, List.mem_cons]
      aesop

/-- INTERNAL: Recover the entire occupancy description of an accepted
ordered defect from the executable classifier, and conversely. -/
theorem classify_defect_iff {n : ℕ} (state : PairedSet n)
    (index : DefectIndex n) :
    (classifyState state).val = .defect index.emptyPair index.fullPair ↔
      (∀ i, ((i, false) ∉ state ∧ (i, true) ∉ state) ↔ i = index.emptyPair) ∧
      (∀ i, ((i, false) ∈ state ∧ (i, true) ∈ state) ↔ i = index.fullPair) := by
  classical
  constructor
  · intro hclass
    have hvalue := classify_value state
    rw [hclass] at hvalue
    have hresult : (List.finRange n).foldl (scanPair state) (none, none, false) =
        (some index.emptyPair, some index.fullPair, false) := by
      generalize (List.finRange n).foldl (scanPair state) (none, none, false) = result
        at hvalue ⊢
      rcases result with ⟨empty, full, flag⟩
      cases flag <;> cases empty <;> cases full
      all_goals simp only [Bool.false_eq_true, if_true, if_false] at hvalue ⊢
      all_goals first
        | cases hvalue
        | (split_ifs at hvalue <;> simp_all)
    obtain ⟨_, he, hf⟩ := scan_fold_false state (List.finRange n)
      (none, none, false) (by rw [hresult])
    constructor
    · intro i
      have hi := he i
      simpa [hresult, eq_comm] using hi.symm
    · intro i
      have hi := hf i
      simpa [hresult, eq_comm] using hi.symm
  · rintro ⟨he, hf⟩
    let scan := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) =>
      if i = index.emptyPair then
        if acc.1.isSome then (acc.1, acc.2.1, true)
        else (some i, acc.2.1, acc.2.2)
      else if i = index.fullPair then
        if acc.2.1.isSome then (acc.1, acc.2.1, true)
        else (acc.1, some i, acc.2.2)
      else acc
    have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
        scanPair state acc i = scan acc i := by
      have hei := he i
      have hfi := hf i
      by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
        simp_all [scanPair, scan]
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
        by_cases hei : i = index.emptyPair
        · subst i
          simp [scan, hi, index.distinct.symm]
        · by_cases hfi : i = index.fullPair
          · subst i
            simp [scan, hi, hei, index.distinct]
          · simp [scan, hei, hfi, Ne.symm hei, Ne.symm hfi]
    rw [classify_value]
    rw [show scanPair state = scan from funext (fun acc => funext (hstep acc))]
    simp [hfold (List.finRange n) (List.nodup_finRange n), index.distinct]

/-- INTERNAL: Ordinary pairs in one defect class exclude its empty and
full pair. They carry the n-2 free Boolean choices. -/
private def ordinaryPairs {n : ℕ} (index : DefectIndex n) : Finset (Fin n) :=
  (Finset.univ.erase index.emptyPair).erase index.fullPair

/-- INTERNAL: Encode a subset of the ordinary pairs by choosing y on that
subset and x on its complement, with both elements at the full pair. -/
private def defectChoiceState {n : ℕ} (index : DefectIndex n)
    (A : Finset (Fin n)) : PairedSet n :=
  (ordinaryPairs index).image (fun i => (i, decide (i ∈ A))) ∪
    {(index.fullPair, false), (index.fullPair, true)}

/-- INTERNAL: Membership in the encoded defect state recovers every free
Boolean choice without referring to a rank or independence oracle. -/
private theorem defect_choice_membership {n : ℕ} (index : DefectIndex n)
    (A : Finset (Fin n)) (i : Fin n) :
    ((i, false) ∈ defectChoiceState index A ↔
      (i ∈ ordinaryPairs index ∧ i ∉ A) ∨ i = index.fullPair) ∧
    ((i, true) ∈ defectChoiceState index A ↔
      (i ∈ ordinaryPairs index ∧ i ∈ A) ∨ i = index.fullPair) := by
  classical
  simp [defectChoiceState, or_comm]

/-- INTERNAL: The classifier accepts the encoded defect state for each
Boolean assignment on its ordinary pairs. -/
private theorem defect_choice_classified {n : ℕ} (index : DefectIndex n)
    (A : Finset (Fin n)) :
    (classifyState (defectChoiceState index A)).val =
      .defect index.emptyPair index.fullPair := by
  apply (classify_defect_iff _ index).mpr
  constructor <;> intro i
  all_goals
    rw [(defect_choice_membership index A i).1,
      (defect_choice_membership index A i).2]
    simp only [ordinaryPairs, Finset.mem_erase, Finset.mem_univ, and_true]
    by_cases he : i = index.emptyPair <;> by_cases hf : i = index.fullPair <;>
      by_cases hA : i ∈ A <;> simp_all [index.distinct, index.distinct.symm]

/-- INTERNAL: Every accepted defect state is recovered from the subset of
ordinary pairs at which it occupies y. This is the surjectivity half of the
initialization counting argument. -/
private theorem defect_choice_complete {n : ℕ} (index : DefectIndex n)
    (state : PairedSet n)
    (hkind : (classifyState state).val = .defect index.emptyPair index.fullPair) :
    defectChoiceState index
      ((ordinaryPairs index).filter (fun i => (i, true) ∈ state)) = state := by
  classical
  obtain ⟨he, hf⟩ := (classify_defect_iff state index).mp hkind
  ext ⟨i, b⟩
  have hei := he i
  have hfi := hf i
  cases b
  all_goals
    first | rw [(defect_choice_membership index _ i).1]
          | rw [(defect_choice_membership index _ i).2]
    simp only [ordinaryPairs, Finset.mem_erase, Finset.mem_univ, and_true,
      Finset.mem_filter]
    by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state
    all_goals simp only [hx, hy] at hei hfi ⊢
    all_goals tauto


/-- INTERNAL: Subsets of the ordinary pairs are recovered injectively from
their encoded defect states. -/
private theorem defect_choice_injective {n : ℕ} (index : DefectIndex n)
    (A B : Finset (Fin n)) (hA : A ⊆ ordinaryPairs index)
    (hB : B ⊆ ordinaryPairs index)
    (heq : defectChoiceState index A = defectChoiceState index B) : A = B := by
  classical
  ext i
  by_cases hi : i ∈ ordinaryPairs index
  · have hfull : i ≠ index.fullPair := (Finset.mem_erase.mp hi).1
    have hmem : ((i, true) ∈ defectChoiceState index A) ↔
        ((i, true) ∈ defectChoiceState index B) := by rw [heq]
    rw [(defect_choice_membership index A i).2,
      (defect_choice_membership index B i).2] at hmem
    simpa [hi, hfull] using hmem
  · have hnA : i ∉ A := fun h => hi (hA h)
    have hnB : i ∉ B := fun h => hi (hB h)
    simp [hnA, hnB]

/-- PAPER: main.tex:1148-1151
At q=1 an ordered defect has one free Boolean choice at each of the n-2
ordinary pairs; its operational partition sum is therefore 2^(n-2). -/
theorem defect_partition_one {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (index : DefectIndex n) :
    FirstPhaseFailure.defectPartition r o₁ o₂ 1 index = (2 : ℚ) ^ (n - 2) := by
  classical
  have hcard : (ordinaryPairs index).card = n - 2 := by
    unfold ordinaryPairs
    rw [Finset.card_erase_of_mem (by simp [index.distinct.symm]),
      Finset.card_erase_of_mem (Finset.mem_univ index.emptyPair), Finset.card_univ]
    simp only [Fintype.card_fin]
    omega
  have hsum : (∑ A ∈ (ordinaryPairs index).powerset, (1 : ℚ)) =
      ∑ state ∈ Finset.univ.filter (fun state : PairedSet n =>
        (classifyState state).val = .defect index.emptyPair index.fullPair), (1 : ℚ) := by
    refine Finset.sum_bij (fun A _ => defectChoiceState index A) ?_ ?_ ?_ ?_
    · intro A _
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact defect_choice_classified index A
    · intro A hA B hB heq
      exact defect_choice_injective index A B
        (Finset.mem_powerset.mp hA) (Finset.mem_powerset.mp hB) heq
    · intro state hstate
      refine ⟨(ordinaryPairs index).filter (fun i => (i, true) ∈ state),
        Finset.mem_powerset.mpr (Finset.filter_subset _ _), ?_⟩
      exact defect_choice_complete index state (Finset.mem_filter.mp hstate).2
    · intro A _
      rfl
  unfold FirstPhaseFailure.defectPartition
  simp only [one_pow]
  rw [← Finset.sum_filter, ← hsum]
  simp [Finset.card_powerset, hcard]

/-- PAPER: main.tex:1148-1151
The initial multiplier four is ideal whenever an ordered defect type exists.
The statement includes the vacuous defect families at `n = 0` and `n = 1`.
Its counting proof must characterize the executable classifier's defect fiber,
rather than assume an independent mathematical state classifier. -/
theorem initial_ideal_multiplier {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (index : DefectIndex n) :
    TransversalPartition.partitionSum r o₁ o₂ 1 /
      FirstPhaseFailure.defectPartition r o₁ o₂ 1 index = 4 := by
  have hn : 2 ≤ n := by
    by_contra h
    apply index.distinct
    apply Fin.ext
    omega
  rw [defect_partition_one]
  have hC : TransversalPartition.partitionSum r o₁ o₂ 1 = (2 : ℚ) ^ n := by
    simp [TransversalPartition.partitionSum]
  rw [hC, show n = (n - 2) + 2 by omega, pow_add]
  norm_num

end CountingMatroid.Analysis.InitialMultipliersGood
