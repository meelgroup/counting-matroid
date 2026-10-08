import CountingMatroid.Model.Subroutines

set_option autoImplicit false

/-!
The first augmentation from the empty common independent set can be found by
scanning singleton queries. This file implements that scan through the two
original charged oracles. It handles rank one, including infeasible inputs;
it does not implement subsequent augmentations for larger ranks.
-/

namespace CountingMatroid.Analysis.RankOneFeasibility

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open scoped Classical

/-- INTERNAL: Test one singleton through both original oracles and retain the
Boolean recording whether the scan has found a common independent singleton.
TEXLINE: main.tex:283-289 -/
def singletonStep {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (found : Bool) (i : Fin n) : Arlib.Computation.Charged Op Cell Bool := do
  let candidate ← insertElement ∅ i
  let query ← encodeQuery candidate
  let first ← oracleQuery false o₁ query
  let second ← oracleQuery true o₂ query
  let common ← Arlib.Computation.Charged.op (Op.word .band) (first && second)
  Arlib.Computation.Charged.op (Op.word .bor) (found || common)

/-- INTERNAL: Bounded scan for the first possible common-independent-set
augmentation. No matroid promise is needed for termination.
TEXLINE: main.tex:283-289 -/
def singletonScan {n : ℕ} (o₁ o₂ : IndependenceOracle n) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.foldl (singletonStep o₁ o₂) (List.finRange n) false

/-- INTERNAL: Under exact oracle answers the scan's single-step invariant is
that its flag records a previously found or newly tested independent singleton. -/
theorem singletonStep_val {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (found : Bool) (i : Fin n) :
    (singletonStep o₁ o₂ found i).val =
      (found || decide (M₁.Indep {i} ∧ M₂.Indep {i})) := by
  classical
  have hdecode : decode (fun j : Fin n => decide (j ∈ ({i} : Finset (Fin n)))) =
      ({i} : Set (Fin n)) := by
    ext j
    simp [decode]
  change (found || (o₁ (fun j => decide (j ∈ ({i} : Finset (Fin n)))) &&
    o₂ (fun j => decide (j ∈ ({i} : Finset (Fin n)))))) = _
  rw [h₁, h₂, hdecode]
  by_cases hfirst : M₁.Indep {i} <;> by_cases hsecond : M₂.Indep {i} <;>
    simp [hfirst, hsecond]

/-- INTERNAL: The bounded first-augmentation scan accepts exactly when the
two matroids have a common independent singleton, equivalently a size-one
common independent set. No shared-rank hypothesis is needed for this scan.
TEXLINE: main.tex:283-289 -/
theorem singletonScan_correct {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) :
    (singletonScan o₁ o₂).val = decide
      (∃ I : Finset (Fin n), I.card = 1 ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n))) := by
  classical
  have hfold (l : List (Fin n)) (found : Bool) :
      (Arlib.Computation.Charged.foldl (singletonStep o₁ o₂) l found).val = true ↔
        found = true ∨ ∃ i ∈ l, M₁.Indep {i} ∧ M₂.Indep {i} := by
    induction l generalizing found with
    | nil => simp
    | cons i l ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons, ih,
          singletonStep_val M₁ M₂ o₁ o₂ h₁ h₂]
        simp only [Bool.or_eq_true, decide_eq_true_eq, List.mem_cons]
        aesop
  have hcorrect : (singletonScan o₁ o₂).val = true ↔
      ∃ I : Finset (Fin n), I.card = 1 ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
    rw [singletonScan, hfold]
    simp only [Bool.false_eq_true, false_or, List.mem_finRange, true_and]
    constructor
    · rintro ⟨i, hfirst, hsecond⟩
      exact ⟨{i}, Finset.card_singleton i,
        by simpa only [Finset.coe_singleton] using hfirst,
        by simpa only [Finset.coe_singleton] using hsecond⟩
    · rintro ⟨I, hcard, hfirst, hsecond⟩
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hcard
      exact ⟨i, by simpa using hfirst, by simpa using hsecond⟩
  cases hvalue : (singletonScan o₁ o₂).val <;> simp_all

/-- INTERNAL: Exact resource counts for the singleton scan, uniform even for
oracles that do not represent matroids. Each singleton uses two oracle calls,
one insertion, quadratic query encoding, and two Boolean operations.
TEXLINE: main.tex:283-289 -/
theorem singletonScan_costs {n : ℕ} (o₁ o₂ : IndependenceOracle n) :
    oracleCalls (singletonScan o₁ o₂) = 2 * n ∧
      otherSteps (singletonScan o₁ o₂) = n * (n * (n + 1) + 3) := by
  let price (op : Op) :=
    (if op = Op.word .store then 1 else 0) +
    (if op = Op.word .load then n * (n + 1) else 0) +
    (if op = Op.oracleFirst then 1 else 0) +
    (if op = Op.oracleSecond then 1 else 0) +
    (if op = Op.word .band then 1 else 0) +
    (if op = Op.word .bor then 1 else 0)
  have hstep (found : Bool) (i : Fin n) (op : Op) :
      (singletonStep o₁ o₂ found i).cost op = price op := by
    simp [singletonStep, insertElement, encodeQuery, oracleQuery, price,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many, Nat.add_assoc]
  have hfold (l : List (Fin n)) (found : Bool) (op : Op) :
      (Arlib.Computation.Charged.foldl (singletonStep o₁ o₂) l found).cost op =
        l.length * price op := by
    induction l generalizing found with
    | nil => simp
    | cons i l ih =>
        rw [Arlib.Computation.Charged.cost_foldl_cons]
        simp only [Pi.add_apply, hstep, ih, List.length_cons]
        ring
  have hcost (op : Op) : (singletonScan o₁ o₂).cost op = n * price op := by
    simpa only [singletonScan, List.length_finRange] using
      hfold (List.finRange n) false op
  constructor
  · simp [oracleCalls, hcost, price]
    omega
  · simp [otherSteps, hcost, price, Arlib.Computation.Op.all]
    ring

end CountingMatroid.Analysis.RankOneFeasibility
