import CountingMatroid.Analysis.TransversalPartition
import CountingMatroid.Analysis.BoundedRunPhase
import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card.Arithmetic

set_option autoImplicit false

/-!
A local failure event for the actual charged phase prefixes. A certificate
requires completion, an accurate ratio, and good stored multipliers. First
failure events partition failure of these certificates, including aborts.
The per-phase finite-tape probability estimate remains in the consuming theorem;
it requires the paper's conditional restart and observation analysis and the
adaptive finite-tape coupling. No independence of adjacent phase events is
assumed by this representation.
-/

namespace CountingMatroid.Analysis.FirstPhaseFailure

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Program CountingMatroid.Analysis.BoundedRunPhase

/-- INTERNAL: The unweighted partition sum of one ordered defect class,
evaluated using the program's paired-rank and state-classification scans.
TEXLINE: main.tex:712-735 -/
noncomputable def defectPartition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (index : DefectIndex n) : ℚ := by
  classical
  exact ∑ state : PairedSet n,
    if (classifyState state).val = .defect index.emptyPair index.fullPair then
      q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
    else 0

/-- INTERNAL: The paper's factor-four condition on every table used by a
restart and on the current phase's multipliers, at their respective parameters.
TEXLINE: main.tex:733-735,1207-1285 -/
def GoodStoredMultipliers {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (j : ℕ) (current : AnnealingCursor n) : Prop :=
  let ideal := fun a index =>
    TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a) /
      defectPartition r o₁ o₂ (s.ρ ^ a) index
  (∀ a ≤ j, ∀ index,
    ideal a index / 4 ≤ current.tables a index ∧
      current.tables a index ≤ 4 * ideal a index) ∧
  ∀ index, ideal j index / 4 ≤ current.currentWeights index ∧
    current.currentWeights index ≤ 4 * ideal j index

/-- INTERNAL: A certificate of one actual phase step, retaining its reached
cursor, its product update, and the good tables needed for the next restart.
The prefix is the value of the exact `boundedRun` loop with its actual
allocations. Final-phase tables need no guarantee at the unused level `L`.
TEXLINE: main.tex:1160-1205,1257-1296 -/
def CertifiedPhase {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  let weights := (initialWeights n).val
  let initial : AnnealingCursor n :=
    ⟨(allocateLearnedWeights n s.L weights).val, weights, 1, 0⟩
  let phaseValue := (Arlib.Computation.Charged.repeatFor
    (boundedRunPhase r o₁ o₂ tape s) j (some initial)).val
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  ∃ ratio : ℚ,
    (1 - s.η) / (1 + s.η) ≤ ratio / (C (j + 1) / C j) ∧
    ratio / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η) ∧
    ∃ current next : AnnealingCursor n,
      phaseValue = some current ∧
      (boundedRunPhase r o₁ o₂ tape s j (some current)).val = some next ∧
      next.product = current.product * ratio ∧
      GoodStoredMultipliers r o₁ o₂ s j current ∧
      (j + 1 < s.L → GoodStoredMultipliers r o₁ o₂ s (j + 1) next)

/-- INTERNAL: First failure of the local phase certificates. Earlier
certificates retain the learned-weight invariant, rather than conditioning
only on earlier ratio accuracy.
TEXLINE: main.tex:1271-1285 -/
def FirstFailure {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ) : Prop :=
  (∀ a < j, CertifiedPhase r o₁ o₂ tape s a) ∧
    ¬ CertifiedPhase r o₁ o₂ tape s j

/-- INTERNAL: Failure of the local certificates is covered by the first
failure events of the actual phase prefixes. This is a finite counting union
bound, and makes no independence assumption about adjacent phases.
TEXLINE: main.tex:1271-1285 -/
theorem uncertified_card_le_sum (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (m : ℕ) :
    Set.ncard {bits : List Bool | bits.length = m ∧
      ¬ ∀ j < s.L, CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j} ≤
    ∑ j ∈ Finset.range s.L,
      Set.ncard {bits : List Bool | bits.length = m ∧
        FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s j} := by
  classical
  let bad := fun j => {bits : List Bool | bits.length = m ∧
    FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s j}
  let failures := ⋃ j ∈ Finset.range s.L, bad j
  have hsubset : {bits : List Bool | bits.length = m ∧
      ¬ ∀ j < s.L, CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j} ⊆
      failures := by
    intro bits hb
    have hex : ∃ j, j < s.L ∧
        ¬ CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j := by
      obtain ⟨j, hj⟩ := not_forall.mp hb.2
      obtain ⟨hj, hbad⟩ := not_forall.mp hj
      exact ⟨j, hj, hbad⟩
    let j := Nat.find hex
    have hj : j < s.L ∧
        ¬ CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s j :=
      Nat.find_spec hex
    have hearlier : ∀ a < j,
        CertifiedPhase r o₁ o₂ (fun i => (bits[i]?).getD false) s a := by
      intro a ha
      by_contra hbad
      exact Nat.find_min hex ha ⟨ha.trans hj.1, hbad⟩
    apply Set.mem_iUnion.mpr
    refine ⟨j, Set.mem_iUnion.mpr ⟨Finset.mem_range.mpr hj.1, ?_⟩⟩
    exact ⟨hb.1, hearlier, hj.2⟩
  have hfinite : failures.Finite :=
    (List.finite_length_eq Bool m).subset (by
      intro bits hb
      obtain ⟨j, hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
      exact hb.1)
  exact (Set.ncard_le_ncard hsubset hfinite).trans
    ((Finset.range s.L).set_ncard_biUnion_le bad)

end CountingMatroid.Analysis.FirstPhaseFailure

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · partial · after mechanical handoff rejection, closed `uncertified_card_le_sum` and retained the operational certificate definitions; the unproved per-phase budget remains inside the assigned parent, rather than in a new exported declaration.
* r18 · open · finite-set conversion and ENNReal denominator normalization expose the exact first-failure counting inequality. The uniform conditional suffix estimate still needs restart expectation, stationary-mean observation MSE, learned-table preservation, and finite-tape coverage. Parent imports and uses this budget in a checked finite union bound.
-/
