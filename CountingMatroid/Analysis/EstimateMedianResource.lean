import CountingMatroid.Analysis.SortedInsertValue

/-!
# Resource bounds for the charged rational median

The insertion scan preserves sorted values and has polynomial charged cost
when its input rational encodings have a common bound.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: The word-operation fold in `otherSteps` distributes over
two charged cost vectors. -/
theorem foldl_word_add (l : List Arlib.Computation.Op)
    (f g : Arlib.Computation.Op → ℕ) :
    ∀ a b, l.foldl (fun z x => z + (f x + g x)) (a + b) =
      l.foldl (fun z x => z + f x) a + l.foldl (fun z x => z + g x) b := by
  induction l with
  | nil => simp
  | cons x xs ih =>
      intro a b
      simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        ih (a + f x) (b + g x)

/-- INTERNAL: Nonoracle charges add when charged computations are sequenced. -/
theorem otherSteps_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    otherSteps (p >>= f) = otherSteps p + otherSteps (f p.val) := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := foldl_word_add Arlib.Computation.Op.all
    (fun x => p.cost (Op.word x)) (fun x => (f p.val).cost (Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega

/-- INTERNAL: A bound on each member of a charged list scan bounds its total
nonoracle charge. -/
theorem otherSteps_foldl_le_of_mem {β ι : Type}
    (f : β → ι → Arlib.Computation.Charged Op Cell β)
    (l : List ι) (k : ℕ)
    (h : ∀ b a, a ∈ l → otherSteps (f b a) ≤ k) (b : β) :
    otherSteps (Arlib.Computation.Charged.foldl f l b) ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp [otherSteps]
  | cons a as ih =>
      rw [show Arlib.Computation.Charged.foldl f (a :: as) b =
        f b a >>= fun b' => Arlib.Computation.Charged.foldl f as b' from rfl,
        otherSteps_bind]
      have hfirst := h b a (by simp)
      have htail := ih (fun b' a' ha' => h b' a' (by simp [ha'])) (f b a).val
      simpa [List.length_cons, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
        Nat.add_assoc] using Nat.add_le_add hfirst htail

/-- INTERNAL: A charged rational comparison costs at most the sum of the
operand encoding lengths. -/
theorem ratLess_otherSteps_le (a b : ℚ) :
    otherSteps (ratLess a b) ≤ binaryRatLength a + binaryRatLength b := by
  simp only [otherSteps, ratLess, Arlib.Computation.Charged.cost_opMany]
  simp [Arlib.Computation.Op.all, Arlib.Computation.CostVec.many,
    binaryRatLength, binaryNatLength]
  change a.num.natAbs.log2 + a.den.log2 + 3 +
    (b.num.natAbs.log2 + b.den.log2 + 3) ≤ _
  omega

/-- INTERNAL: Inserting one bounded-length rational costs at most a linear
number of bounded-length comparisons and list operations. -/
theorem sortedInsert_otherSteps_le (value : ℚ) (sorted : List ℚ) (K : ℕ)
    (hv : binaryRatLength value ≤ K)
    (hs : ∀ q ∈ sorted, binaryRatLength q ≤ K) :
    otherSteps (CountingMatroid.Program.sortedInsert value sorted) ≤
      (sorted.length + 1) * (2 * K + 6) := by
  let step : List ℚ × Bool → ℚ → Arlib.Computation.Charged Op Cell (List ℚ × Bool) :=
    fun acc item => do
      if acc.2 then
        let reversed ← consRational item acc.1
        pure (reversed, true)
      else
        let before ← ratLess value item
        if before then
          let reversed ← consRational value acc.1
          let reversed ← consRational item reversed
          pure (reversed, true)
        else
          let reversed ← consRational item acc.1
          pure (reversed, false)
  have hstep (acc : List ℚ × Bool) (item : ℚ) (hi : item ∈ sorted) :
      otherSteps (step acc item) ≤ 2 * K + 2 := by
    rcases acc with ⟨rev, flag⟩
    cases flag
    · have hless := ratLess_otherSteps_le value item
      have hitem := hs item hi
      by_cases hcmp : value < item
      · have hcost : otherSteps (step (rev, false) item) =
            otherSteps (ratLess value item) + 2 := by
          simp [step, hcmp, otherSteps_bind, ratLess, consRational,
            otherSteps, Arlib.Computation.Op.all]
        rw [hcost]
        omega
      · have hcost : otherSteps (step (rev, false) item) =
            otherSteps (ratLess value item) + 1 := by
          simp [step, hcmp, otherSteps_bind, ratLess, consRational,
            otherSteps, Arlib.Computation.Op.all]
        rw [hcost]
        omega
    · simp [step, consRational, otherSteps, Arlib.Computation.Op.all]
  have hfold := otherSteps_foldl_le_of_mem step sorted (2 * K + 2)
    (fun acc item hi => hstep acc item hi) (([] : List ℚ), false)
  have hstep_length (acc : List ℚ × Bool) (item : ℚ) :
      (step acc item).val.1.length ≤ acc.1.length + 2 := by
    rcases acc with ⟨rev, flag⟩
    cases flag <;> by_cases hcmp : value < item <;>
      simp [step, hcmp, ratLess, consRational] <;> omega
  have hfold_length : ∀ (l : List ℚ) (acc : List ℚ × Bool),
      (Arlib.Computation.Charged.foldl step l acc).val.1.length ≤
        acc.1.length + 2 * l.length := by
    intro l
    induction l with
    | nil => intro acc; simp
    | cons item l ih =>
        intro acc
        rw [Arlib.Computation.Charged.val_foldl_cons]
        have htail := ih (step acc item).val
        have hhead := hstep_length acc item
        simp only [List.length_cons]
        omega
  have hlen : (Arlib.Computation.Charged.foldl step sorted ([], false)).val.1.length ≤
      2 * sorted.length := by
    simpa using hfold_length sorted ([], false)
  unfold CountingMatroid.Program.sortedInsert
  change otherSteps (do
    let (reversed, inserted) ← Arlib.Computation.Charged.foldl step sorted ([], false)
    let reversed ← if inserted then pure reversed else consRational value reversed
    reverseRationals reversed) ≤ _
  simp only [otherSteps_bind]
  have htail : otherSteps
      (if (Arlib.Computation.Charged.foldl step sorted ([], false)).val.2 then
        do
          let reversed ← pure (Arlib.Computation.Charged.foldl step sorted ([], false)).val.1
          reverseRationals reversed
      else do
        let reversed ← consRational value
          (Arlib.Computation.Charged.foldl step sorted ([], false)).val.1
        reverseRationals reversed) ≤ 2 * sorted.length + 3 := by
    cases hflag : (Arlib.Computation.Charged.foldl step sorted ([], false)).val.2 <;>
      simp [consRational, reverseRationals, otherSteps,
        Arlib.Computation.Op.all] <;>
      omega
  calc
    _ ≤ sorted.length * (2 * K + 2) + (2 * sorted.length + 3) :=
      Nat.add_le_add hfold htail
    _ ≤ (sorted.length + 1) * (2 * K + 6) := by nlinarith

/-- INTERNAL: The charged median scan retains sortedness, bounded element
encodings, and the expected list length after every insertion. -/
theorem median_scan_properties (xs acc : List ℚ) (K : ℕ)
    (haccSort : acc.Pairwise (· ≤ ·))
    (haccSize : ∀ q ∈ acc, binaryRatLength q ≤ K)
    (hxsSize : ∀ q ∈ xs, binaryRatLength q ≤ K) :
    let out := (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      xs acc).val
    out.Pairwise (· ≤ ·) ∧
      (∀ q ∈ out, binaryRatLength q ≤ K) ∧
      out.length = acc.length + xs.length := by
  induction xs generalizing acc with
  | nil => exact ⟨haccSort, haccSize, by simp⟩
  | cons value xs ih =>
      have hv : binaryRatLength value ≤ K := hxsSize value (by simp)
      have htail : ∀ q ∈ xs, binaryRatLength q ≤ K := by
        intro q hq
        exact hxsSize q (by simp [hq])
      have hins := CountingMatroid.Analysis.sortedInsert_value_eq
        value acc haccSort
      have hsort : (acc.orderedInsert (· ≤ ·) value).Pairwise (· ≤ ·) :=
        haccSort.orderedInsert value acc
      have hsize : ∀ q ∈ acc.orderedInsert (· ≤ ·) value,
          binaryRatLength q ≤ K := by
        intro q hq
        rcases (List.mem_orderedInsert (· ≤ ·)).mp hq with rfl | ha
        · exact hv
        · exact haccSize q ha
      have hnext := ih (acc.orderedInsert (· ≤ ·) value) hsort hsize htail
      simpa [Arlib.Computation.Charged.val_foldl_cons, hins,
        List.orderedInsert_length, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hnext

/-- INTERNAL: The charged insertion-sort scan takes quadratic many bounded
rational comparisons. -/
theorem median_scan_otherSteps_le (xs acc : List ℚ) (K : ℕ)
    (haccSort : acc.Pairwise (· ≤ ·))
    (haccSize : ∀ q ∈ acc, binaryRatLength q ≤ K)
    (hxsSize : ∀ q ∈ xs, binaryRatLength q ≤ K) :
    otherSteps (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      xs acc) ≤ xs.length * (acc.length + xs.length + 1) * (2 * K + 6) := by
  induction xs generalizing acc with
  | nil => simp [otherSteps]
  | cons value xs ih =>
      have hv : binaryRatLength value ≤ K := hxsSize value (by simp)
      have htailSize : ∀ q ∈ xs, binaryRatLength q ≤ K := by
        intro q hq
        exact hxsSize q (by simp [hq])
      let next := (CountingMatroid.Program.sortedInsert value acc).val
      have hins : next = acc.orderedInsert (· ≤ ·) value :=
        CountingMatroid.Analysis.sortedInsert_value_eq value acc haccSort
      have hnextSort : next.Pairwise (· ≤ ·) := by
        rw [hins]
        exact haccSort.orderedInsert value acc
      have hnextSize : ∀ q ∈ next, binaryRatLength q ≤ K := by
        intro q hq
        rw [hins] at hq
        rcases (List.mem_orderedInsert (· ≤ ·)).mp hq with rfl | ha
        · exact hv
        · exact haccSize q ha
      have hnextLen : next.length = acc.length + 1 := by
        rw [hins]
        exact List.orderedInsert_length (· ≤ ·) acc value
      have hhead := sortedInsert_otherSteps_le value acc K hv haccSize
      have htail := ih next hnextSort hnextSize htailSize
      have hhead' : otherSteps (CountingMatroid.Program.sortedInsert value acc) ≤
          (acc.length + (xs.length + 1) + 1) * (2 * K + 6) := by
        apply le_trans hhead
        exact Nat.mul_le_mul_right _ (by omega)
      have htail' : otherSteps (Arlib.Computation.Charged.foldl
          (fun acc value => CountingMatroid.Program.sortedInsert value acc)
          xs next) ≤ xs.length *
            ((acc.length + (xs.length + 1) + 1) * (2 * K + 6)) := by
        rw [hnextLen] at htail
        convert htail using 1 <;> ring
      change otherSteps ((CountingMatroid.Program.sortedInsert value acc) >>=
        fun next => Arlib.Computation.Charged.foldl
          (fun acc value => CountingMatroid.Program.sortedInsert value acc)
          xs next) ≤ _
      rw [otherSteps_bind]
      change otherSteps (CountingMatroid.Program.sortedInsert value acc) +
        otherSteps (Arlib.Computation.Charged.foldl
          (fun acc value => CountingMatroid.Program.sortedInsert value acc)
          xs next) ≤ _
      calc
        _ ≤ (acc.length + (xs.length + 1) + 1) * (2 * K + 6) +
            xs.length * ((acc.length + (xs.length + 1) + 1) * (2 * K + 6)) :=
          Nat.add_le_add hhead' htail'
        _ = (xs.length + 1) * (acc.length + (xs.length + 1) + 1) *
            (2 * K + 6) := by ring

/-- INTERNAL: The charged median computation has polynomial cost when each
input rational has bounded encoding length. -/
theorem medianRational_otherSteps_le (values : List ℚ) (K : ℕ)
    (hsize : ∀ q ∈ values, binaryRatLength q ≤ K) :
    otherSteps (CountingMatroid.Program.medianRational values) ≤
      (values.length + 1) ^ 2 * (2 * K + 8) := by
  let sorted := (Arlib.Computation.Charged.foldl
    (fun acc value => CountingMatroid.Program.sortedInsert value acc)
    values ([] : List ℚ)).val
  have hsortedLength : sorted.length = values.length := by
    have hprops := median_scan_properties values [] K
      (by simp) (by simp) hsize
    simpa [sorted] using hprops.2.2
  have hscan := median_scan_otherSteps_le values [] K
    (by simp) (by simp) hsize
  unfold CountingMatroid.Program.medianRational
  simp only [otherSteps_bind]
  have hhalf : otherSteps (halfNat values.length) = 1 := by
    simp [halfNat, otherSteps, Arlib.Computation.Op.all]
  have hnth : otherSteps (nthRational sorted (values.length / 2)) =
      sorted.length + 1 := by
    simp [nthRational, otherSteps, Arlib.Computation.Op.all]
  have hhalfVal : (halfNat values.length).val = values.length / 2 := rfl
  have hpure (q : ℚ) :
      otherSteps (pure q : Arlib.Computation.Charged Op Cell ℚ) = 0 := by
    simp [otherSteps]
  simp only [hhalfVal, hpure, Nat.add_zero]
  rw [hhalf, hnth, hsortedLength]
  have hscan' : otherSteps (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      values []) ≤ values.length * (values.length + 1) * (2 * K + 6) := by
    simpa using hscan
  have hscan'' : otherSteps (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      values []) ≤ values.length * (values.length + 1) * (2 * K + 8) :=
    le_trans hscan' (Nat.mul_le_mul_left _ (by omega))
  have hlast : 1 + (values.length + 1) ≤
      (values.length + 1) * (2 * K + 8) := by nlinarith
  calc
    _ ≤ values.length * (values.length + 1) * (2 * K + 8) +
        (values.length + 1) * (2 * K + 8) :=
      Nat.add_le_add hscan'' hlast
    _ = (values.length + 1) ^ 2 * (2 * K + 8) := by ring

/-- INTERNAL: Inserting nonnegative observations into the charged median scan
preserves nonnegativity of its eventual answer. -/
theorem medianRational_nonneg (values : List ℚ)
    (hvalues : ∀ q ∈ values, 0 ≤ q) :
    0 ≤ (CountingMatroid.Program.medianRational values).val := by
  have hscan : ∀ (xs acc : List ℚ), acc.Pairwise (· ≤ ·) →
      (∀ q ∈ acc, 0 ≤ q) → (∀ q ∈ xs, 0 ≤ q) →
      ∀ q ∈ (Arlib.Computation.Charged.foldl
        (fun acc value => CountingMatroid.Program.sortedInsert value acc)
        xs acc).val, 0 ≤ q := by
    intro xs
    induction xs with
    | nil => intro acc _ hacc _ q hq; simpa using hacc q hq
    | cons value xs ih =>
        intro acc hsorted hacc hxs q hq
        have hins := CountingMatroid.Analysis.sortedInsert_value_eq value acc hsorted
        rw [Arlib.Computation.Charged.val_foldl_cons] at hq
        rw [hins] at hq
        apply ih (acc.orderedInsert (· ≤ ·) value)
          (hsorted.orderedInsert value acc) _ _ q hq
        · intro z hz
          rcases (List.mem_orderedInsert (· ≤ ·)).mp hz with rfl | ha
          · exact hxs z (by simp)
          · exact hacc z ha
        · intro z hz
          exact hxs z (by simp [hz])
  have hall := hscan values [] (by simp) (by simp) hvalues
  unfold CountingMatroid.Program.medianRational
  simp only [Arlib.Computation.Charged.val_bind, halfNat, nthRational,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany,
    Arlib.Computation.Charged.val_pure]
  cases hget : (Arlib.Computation.Charged.foldl
      (fun acc value => CountingMatroid.Program.sortedInsert value acc)
      values []).val[values.length / 2]? with
  | none => simp
  | some q =>
      simp
      exact hall q (List.mem_of_getElem? hget)

end CountingMatroid.Analysis.ResourceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · proved · extracted and closed the median length, sign, and charge invariants used by the estimator.
-/
