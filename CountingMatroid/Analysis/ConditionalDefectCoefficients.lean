import CountingMatroid.Analysis.InitialMultipliersGood

set_option autoImplicit false

/-!
Conditional transversal and defect totals for the operational rank weights.
The empty assignment recovers the existing partition sums. Positivity and
binary splitting below concern these finite sums; the quadratic signature
inequalities are separate mathematical obligations.
-/

namespace CountingMatroid.Analysis.ConditionalDefectCoefficients

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.TransversalPartition

/-- PAPER: main.tex:383-386
A partial transversal specifies the selected element at each assigned pair. -/
abbrev Assignment (n : ℕ) := Fin n → Option Bool

/-- PAPER: main.tex:383-389
Respecting an assignment requires the chosen element and excludes its mate. -/
def Respects {n : ℕ} (σ : Assignment n) (state : PairedSet n) : Prop :=
  ∀ i b, σ i = some b → (i, b) ∈ state ∧ (i, !b) ∉ state

/-- INTERNAL: Express the same assignment on the original subset indexing
transversals, with false selecting x and true selecting y.
TEXLINE: main.tex:383-389 -/
def SubsetRespects {n : ℕ} (σ : Assignment n) (A : Finset (Fin n)) : Prop :=
  ∀ i b, σ i = some b → decide (i ∉ A) = b

/-- PAPER: main.tex:383-392
The conditional transversal total uses the actual operational deficiency. -/
noncomputable def transversalTotal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n) : ℚ := by
  classical
  exact ∑ A : Finset (Fin n),
    if SubsetRespects σ A then q ^ transversalDeficiency r o₁ o₂ A else 0

/-- PAPER: main.tex:386-392
The conditional unmultiplied ordered-defect total uses the operational
classifier and paired-rank scan, with the empty/full indices unassigned. -/
noncomputable def defectTotal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (index : DefectIndex n) : ℚ := by
  classical
  exact ∑ state : PairedSet n,
    if Respects σ state ∧
      (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0

/-- INTERNAL: The original-subset and paired-state assignment predicates
agree on the existing transversal encoding.
TEXLINE: main.tex:383-389 -/
theorem subset_respects_iff {n : ℕ} (σ : Assignment n) (A : Finset (Fin n)) :
    SubsetRespects σ A ↔ Respects σ (transversalState A) := by
  constructor <;> intro h i b hb
  · have hi := h i b hb
    cases b <;> by_cases hm : i ∈ A <;> simp_all [transversalState]
  · have hi := h i b hb
    cases b <;> by_cases hm : i ∈ A <;> simp_all [transversalState]

/-- INTERNAL: The root transversal total is the partition sum already used
by the program analysis.
TEXLINE: main.tex:390-392 -/
theorem transversal_total_empty {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) :
    transversalTotal r o₁ o₂ q (fun _ => none) = partitionSum r o₁ o₂ q := by
  classical
  simp [transversalTotal, SubsetRespects, partitionSum]

/-- INTERNAL: The root defect total is the existing operational defect sum.
TEXLINE: main.tex:390-392 -/
theorem defect_total_empty {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (index : DefectIndex n) :
    defectTotal r o₁ o₂ q (fun _ => none) index =
      FirstPhaseFailure.defectPartition r o₁ o₂ q index := by
  classical
  simp [defectTotal, Respects, FirstPhaseFailure.defectPartition]

/-- PAPER: main.tex:392
Every conditional transversal total is positive: a partial assignment has
a transversal completion and every operational rank weight is positive. -/
theorem transversal_total_pos {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q) (σ : Assignment n) :
    0 < transversalTotal r o₁ o₂ q σ := by
  classical
  let A := Finset.univ.filter (fun i => σ i = some false)
  have hA : SubsetRespects σ A := by
    intro i b hb
    cases b <;> simp [A, hb]
  have hterm : 0 < (if SubsetRespects σ A then
      q ^ transversalDeficiency r o₁ o₂ A else 0) := by
    rw [if_pos hA]
    exact pow_pos hq _
  apply hterm.trans_le
  unfold transversalTotal
  exact Finset.single_le_sum
    (f := fun B => if SubsetRespects σ B then q ^ transversalDeficiency r o₁ o₂ B else 0)
    (fun B _ => by
    split_ifs
    · exact (pow_pos hq _).le
    · exact le_rfl) (Finset.mem_univ A)

/-- INTERNAL: Specifying an unassigned pair adds exactly its selected bit
to the original-subset assignment predicate.
TEXLINE: main.tex:810-817 -/
theorem subset_respects_update {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (b : Bool) (A : Finset (Fin n)) :
    SubsetRespects (Function.update σ k (some b)) A ↔
      SubsetRespects σ A ∧ decide (k ∉ A) = b := by
  classical
  constructor
  · intro h
    refine ⟨?_, h k b (by simp)⟩
    intro i a hi
    have hik : i ≠ k := by rintro rfl; rw [hk] at hi; cases hi
    apply h i a
    simpa [Function.update_of_ne hik] using hi
  · rintro ⟨h, hb⟩ i a hi
    by_cases hik : i = k
    · subst i
      have hab : b = a := by simpa using hi
      exact hb.trans hab
    · apply h i a
      simpa [Function.update_of_ne hik] using hi

/-- PAPER: main.tex:815-817
The two children at an unassigned pair partition the conditional
transversal total. -/
theorem transversal_total_split {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (σ : Assignment n)
    (k : Fin n) (hk : σ k = none) :
    transversalTotal r o₁ o₂ q (Function.update σ k (some false)) +
      transversalTotal r o₁ o₂ q (Function.update σ k (some true)) =
        transversalTotal r o₁ o₂ q σ := by
  classical
  unfold transversalTotal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro A _
  rw [subset_respects_update σ k hk false A, subset_respects_update σ k hk true A]
  by_cases hA : SubsetRespects σ A <;> by_cases hmem : k ∈ A <;> simp [hA, hmem]

/-- INTERNAL: Complete a partial assignment to the specified defect class;
unassigned ordinary pairs select x.
TEXLINE: main.tex:383-392 -/
def defectCompletion {n : ℕ} (σ : Assignment n) (index : DefectIndex n) : PairedSet n :=
  ((Finset.univ.erase index.emptyPair).erase index.fullPair).image
    (fun i => (i, (σ i).getD false)) ∪
      {(index.fullPair, false), (index.fullPair, true)}

/-- INTERNAL: The ordinary pairs of a defect completion have exactly their
prescribed/default bit; the full pair has both bits and the empty pair neither.
TEXLINE: main.tex:383-392 -/
theorem mem_defect_completion {n : ℕ} (σ : Assignment n) (index : DefectIndex n)
    (i : Fin n) (b : Bool) :
    (i, b) ∈ defectCompletion σ index ↔
      (i ≠ index.emptyPair ∧ i ≠ index.fullPair ∧ (σ i).getD false = b) ∨
        i = index.fullPair := by
  classical
  cases b <;> simp [defectCompletion] <;> tauto

/-- INTERNAL: The existing executable classifier accepts each conditioned
defect completion using the existing state-shape characterization.
TEXLINE: main.tex:383-392 -/
theorem defect_completion_classified {n : ℕ} (σ : Assignment n) (index : DefectIndex n) :
    (classifyState (defectCompletion σ index)).val =
      .defect index.emptyPair index.fullPair := by
  apply (InitialMultipliersGood.classify_defect_iff _ index).mpr
  constructor <;> intro i
  all_goals
    rw [mem_defect_completion, mem_defect_completion]
    cases hb : (σ i).getD false <;>
      by_cases he : i = index.emptyPair <;> by_cases hf : i = index.fullPair <;>
        simp_all [index.distinct, index.distinct.symm]

/-- INTERNAL: The conditioned defect completion respects the assignment
when its empty and full pairs are unassigned.
TEXLINE: main.tex:383-392 -/
theorem defect_completion_respects {n : ℕ} (σ : Assignment n) (index : DefectIndex n)
    (he : σ index.emptyPair = none) (hf : σ index.fullPair = none) :
    Respects σ (defectCompletion σ index) := by
  intro i b hb
  have hie : i ≠ index.emptyPair := by rintro rfl; rw [he] at hb; cases hb
  have hif : i ≠ index.fullPair := by rintro rfl; rw [hf] at hb; cases hb
  constructor <;> rw [mem_defect_completion]
  · simp [hie, hif, hb]
  · cases b <;> simp [hie, hif, hb]

/-- PAPER: main.tex:392
Conditional defect totals are positive whenever their empty and full pairs
are unassigned, as required in the paper's coefficient inequalities. -/
theorem defect_total_pos {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q)
    (σ : Assignment n) (index : DefectIndex n)
    (he : σ index.emptyPair = none) (hf : σ index.fullPair = none) :
    0 < defectTotal r o₁ o₂ q σ index := by
  classical
  let S := defectCompletion σ index
  have hS : Respects σ S ∧ (classifyState S).val =
      .defect index.emptyPair index.fullPair :=
    ⟨defect_completion_respects σ index he hf, defect_completion_classified σ index⟩
  let term := fun state : PairedSet n =>
    if Respects σ state ∧
      (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0
  have hterm : 0 < term S := by
    dsimp only [term]
    rw [if_pos hS]
    exact pow_pos hq _
  exact hterm.trans_le (Finset.single_le_sum (f := term) (fun state _ => by
    dsimp only [term]
    split_ifs
    · exact (pow_pos hq _).le
    · exact le_rfl) (Finset.mem_univ S))

end CountingMatroid.Analysis.ConditionalDefectCoefficients
