import CountingMatroid.Analysis.BoundedRunPhase
import CountingMatroid.Analysis.TransversalPartition

set_option autoImplicit false

/-!
The phase history below is the value of each prefix of the actual bounded-run
fold, including its absorbing aborted state. Successful local ratio steps
give the product witness used by the lower-tail proof. This is a
deterministic operational representation, not a phase probability estimate.
-/

namespace CountingMatroid.Analysis.BoundedRunPhaseHistory

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

/-- INTERNAL: The initial cursor is the value of the actual allocations in
`boundedRun`; no independently chosen learned tables are supplied.
TEXLINE: main.tex:1152-1160 -/
noncomputable def initialCursor (n : ℕ) (s : AnnealingSchedule) : AnnealingCursor n :=
  let weights := (initialWeights n).val
  ⟨(allocateLearnedWeights n s.L weights).val, weights, 1, 0⟩

/-- INTERNAL: Prefix states of the actual charged phase fold. `none` retains
all abort branches, rather than conditioning on a completed run.
TEXLINE: main.tex:1160-1205 -/
noncomputable def phaseHistory {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    Option (AnnealingCursor n) :=
  (Arlib.Computation.Charged.repeatFor
    (boundedRunPhase r o₁ o₂ tape s) j (some (initialCursor n s))).val

/-- INTERNAL: Split a charged fold at a prefix while retaining its actual value. -/
private theorem val_foldl_append {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (b : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) b).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs b).val).val := by
  induction xs generalizing b with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f b x).val

/-- INTERNAL: Consecutive history entries are related by the actual phase
body, with the previously reached tables, weights, product and bit cursor.
TEXLINE: main.tex:1160-1205 -/
theorem phaseHistory_succ {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) :
    phaseHistory r o₁ o₂ tape s (j + 1) =
      (boundedRunPhase r o₁ o₂ tape s j
        (phaseHistory r o₁ o₂ tape s j)).val := by
  unfold phaseHistory Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, val_foldl_append]
  rfl

/-- INTERNAL: The returned value is the scaled product in the last entry of
this same operational history; an aborted entry returns zero.
TEXLINE: main.tex:1202-1205 -/
theorem singleRun_eq_phaseHistory {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule) :
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
      match phaseHistory r o₁ o₂ tape s s.L with
      | none => 0
      | some current => ((natPower 2 n).val : ℚ) * current.product := by
  unfold CountingMatroid.Interface.Pseudocode.singleRun boundedRun
  simp only [Arlib.Computation.Charged.val_bind]
  change (match phaseHistory r o₁ o₂ tape s s.L with
    | none => (pure ((0 : ℚ), (0 : ℕ)) :
        Arlib.Computation.Charged Op Cell (ℚ × ℕ))
    | some current => do
        let powerOfTwo ← natPower 2 n
        let scale ← ratOfNat powerOfTwo
        let estimate ← ratMul scale current.product
        pure (estimate, current.bitCursor)).val.1 = _
  cases phaseHistory r o₁ o₂ tape s s.L with
  | none => rfl
  | some current =>
      simp [ratOfNat, ratMul]

/-- INTERNAL: A local good phase requires a successful transition from the
actually reached cursor, positive accumulated products, and the relative
ratio bounds. The quotient of consecutive products recovers the executed
ratio, so a separate independently chosen ratio sequence is unnecessary.
TEXLINE: main.tex:1273-1296 -/
def PhaseRatioStep {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) (j : ℕ) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun k => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ k)
  ∃ current next : AnnealingCursor n,
    phaseHistory r o₁ o₂ tape s j = some current ∧
    (boundedRunPhase r o₁ o₂ tape s j (some current)).val = some next ∧
    0 < current.product ∧ 0 < next.product ∧
    (1 - s.η) / (1 + s.η) ≤
      (next.product / current.product) / (C (j + 1) / C j) ∧
    (next.product / current.product) / (C (j + 1) / C j) ≤
      (1 + s.η) / (1 - s.η)

/-- INTERNAL: Local successful-ratio steps of the actual bounded phase fold
produce the accurate-ratio witness, including a nonaborted final cursor.
The product invariant is proved by cancellation of consecutive positive
accumulated products, rather than assumed as a property of a transcript.
TEXLINE: main.tex:1273-1304 -/
theorem successful_history_product {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (hgood : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
    ∃ R : ℕ → ℚ,
      (∃ current : AnnealingCursor n,
        phaseHistory r o₁ o₂ tape s s.L = some current ∧
        current.product = ∏ j ∈ Finset.range s.L, R j) ∧
      ∀ j < s.L,
        (1 - s.η) / (1 + s.η) ≤ R j / (C (j + 1) / C j) ∧
        R j / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let history := phaseHistory r o₁ o₂ tape s
  let P := fun j => (history j).elim (0 : ℚ) (fun current => current.product)
  let R := fun j => P (j + 1) / P j
  have hzero : history 0 = some (initialCursor n s) := rfl
  have hPzero : P 0 = 1 := rfl
  have hnext (j : ℕ) (hj : j < s.L) :
      ∃ current next : AnnealingCursor n,
        history j = some current ∧ history (j + 1) = some next ∧
        0 < current.product ∧ 0 < next.product ∧
        (1 - s.η) / (1 + s.η) ≤
          (next.product / current.product) /
            (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
              TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ∧
        (next.product / current.product) /
            (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
              TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ≤
          (1 + s.η) / (1 - s.η) := by
    obtain ⟨current, next, hcurrent, hstep, hpos, hpos', hratio⟩ := hgood j hj
    refine ⟨current, next, hcurrent, ?_, hpos, hpos', hratio⟩
    change phaseHistory r o₁ o₂ tape s (j + 1) = some next
    rw [phaseHistory_succ, hcurrent, hstep]
  have hstates (k : ℕ) (hk : k ≤ s.L) :
      ∃ current : AnnealingCursor n, history k = some current ∧
        0 < current.product := by
    cases k with
    | zero => exact ⟨initialCursor n s, hzero, by norm_num [initialCursor]⟩
    | succ k =>
        obtain ⟨current, next, _, hn, _, hp, _⟩ := hnext k (by omega)
        exact ⟨next, hn, hp⟩
  have hPpos (k : ℕ) (hk : k ≤ s.L) : 0 < P k := by
    obtain ⟨current, hc, hp⟩ := hstates k hk
    simpa only [P, hc, Option.elim_some] using hp
  have hprod (k : ℕ) (hk : k ≤ s.L) :
      (∏ j ∈ Finset.range k, R j) = P k := by
    induction k with
    | zero => simp only [Finset.range_zero, Finset.prod_empty, hPzero]
    | succ k ih =>
        rw [Finset.prod_range_succ, ih (by omega)]
        dsimp only [R]
        field_simp [(hPpos k (by omega)).ne']
  refine ⟨R, ?_, ?_⟩
  · obtain ⟨current, hc, _⟩ := hstates s.L le_rfl
    refine ⟨current, hc, ?_⟩
    have hp := hprod s.L le_rfl
    simpa only [P, hc, Option.elim_some] using hp.symm
  · intro j hj
    obtain ⟨current, next, hc, hn, _, _, hr⟩ := hnext j hj
    simpa only [R, P, hc, hn, Option.elim_some] using hr

/-- INTERNAL: Partition unsuccessful histories by the first phase whose
actual transition aborts or whose accumulated-product ratio is inaccurate.
This predicate imposes no nonzero-output guard.
TEXLINE: main.tex:1273-1287 -/
def FirstPhaseRatioFailure {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) : Prop :=
  ∃ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
    (∀ i < j, PhaseRatioStep r o₁ o₂ p tape i) ∧
    ¬ PhaseRatioStep r o₁ o₂ p tape j

/-- INTERNAL: An unsuccessful local-step history is covered by an actual
first unsuccessful phase. This includes aborts without importing their
probability estimate from the downstream lower-tail consumer.
TEXLINE: main.tex:1273-1304 -/
theorem first_phase_failure_of_unsuccessful_history {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (tape : ℕ → Bool)
    (hbad : ¬ ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j) :
    FirstPhaseRatioFailure r o₁ o₂ p tape := by
  classical
  have hex : ∃ j, j < (CountingMatroid.Interface.Pseudocode.setup n p).L ∧
      ¬ PhaseRatioStep r o₁ o₂ p tape j := by
    by_contra hnone
    apply hbad
    intro j hj
    by_contra hjbad
    exact hnone ⟨j, hj, hjbad⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, ?_, (Nat.find_spec hex).2⟩
  intro i hi
  by_contra hibad
  exact Nat.find_min hex hi ⟨hi.trans (Nat.find_spec hex).1, hibad⟩

end CountingMatroid.Analysis.BoundedRunPhaseHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · represented actual phase-fold prefixes; proved their successor relation and final-output equality, reconstructed an accurate-ratio witness from successful local steps, and covered witness failure by the first failed phase. No probability estimate or unproved declaration introduced.
-/
