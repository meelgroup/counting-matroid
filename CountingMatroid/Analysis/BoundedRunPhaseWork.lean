import CountingMatroid.Analysis.PhaseResourcePrimitives
import CountingMatroid.Analysis.BoundedRunPhase
import CountingMatroid.Analysis.RationalHeight
import CountingMatroid.Analysis.RestartPhaseWork
import CountingMatroid.Analysis.ObservePhaseWork
import CountingMatroid.Analysis.FinishPhaseWork

/-!
The full nonoracle-work bound for one bounded annealing phase follows from
proved capped-chain, restart, observation, and finishing cost bounds. Each
bound includes abort paths; the observation and finishing scans carry their
reached rational-size invariants. The explicit sum of these component budgets
is absorbed into `runSize ^ 40`, with the original theorem statement retained.
-/

set_option autoImplicit false
set_option maxHeartbeats 2000000
namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.RestartPhaseWork
open CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: A common encoding bound for the reached observation accumulator. -/
private def phaseWorkSumBudget (S : ℕ) : ℕ :=
  2 * (1 + S * (4 + S * S + 1)) + 2

/-- INTERNAL: Sum the component work envelopes after replacing all schedule
caps and dimensions by their common run-size bound. TEXLINE: main.tex:1348-1440 -/
private def phaseWorkBudget (S : ℕ) : ℕ :=
  S * (4 + S * S) ^ 2 +
  (S * (2 * S + 3) + S *
    (1 + S * (4 + S * S) ^ 2 + (S * S * S + 1) +
      S * (S * (chainBudget S S (S ^ 11) + S * (4 * S + 3) + 3)))) +
  (S * S + 1 + S *
    (1 + chainBudget S S (S ^ 11) +
      recordBudget S S (1 + S * (4 + S * S + 1)))) +
  (S * S + 5 + 2 * (S + 4) + 4 * (S + 4) ^ 2 +
    2 * (phaseWorkSumBudget S + 3 * (S + 4)) ^ 2 +
    S * S * finishEntryBudget S (S + 4)
      (S ^ 11 + S * S * (4 * (S + 4)) + S * (4 * (S + 4)))) +
  (S ^ 11 + phaseWorkSumBudget S + 3 * (S + 4)) ^ 2 +
  (2 + S * S * S + 1)

/-- INTERNAL: Absorb the explicit component polynomial into the prescribed
fortieth-power envelope. TEXLINE: main.tex:1348-1440 -/
private theorem phaseWorkBudget_le (S : ℕ) (hS : 5 ≤ S) :
    phaseWorkBudget S ≤ S ^ 40 := by
  have hpos : 0 < S := by omega
  have hp0 : S ^ 0 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp1 : S ^ 1 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp2 : S ^ 2 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp3 : S ^ 3 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp4 : S ^ 4 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp5 : S ^ 5 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp6 : S ^ 6 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp7 : S ^ 7 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp8 : S ^ 8 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp9 : S ^ 9 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp10 : S ^ 10 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp11 : S ^ 11 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp12 : S ^ 12 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp13 : S ^ 13 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp14 : S ^ 14 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp15 : S ^ 15 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp16 : S ^ 16 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp17 : S ^ 17 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp18 : S ^ 18 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp19 : S ^ 19 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp20 : S ^ 20 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp21 : S ^ 21 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp22 : S ^ 22 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp23 : S ^ 23 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp24 : S ^ 24 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp25 : S ^ 25 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  have hp26 : S ^ 26 ≤ S ^ 26 := Nat.pow_le_pow_right hpos (by omega)
  simp only [pow_zero, pow_one] at hp0 hp1
  have hpoly : phaseWorkBudget S ≤ 20000 * S ^ 26 := by
    unfold phaseWorkBudget phaseWorkSumBudget chainBudget recordBudget finishEntryBudget
    ring_nf
    omega
  have hconstant : 20000 ≤ S ^ 7 := by
    calc
      20000 ≤ 5 ^ 7 := by norm_num
      _ ≤ S ^ 7 := Nat.pow_le_pow_left hS 7
  calc
    phaseWorkBudget S ≤ 20000 * S ^ 26 := hpoly
    _ ≤ S ^ 7 * S ^ 26 := Nat.mul_le_mul_right _ hconstant
    _ = S ^ 33 := by rw [← pow_add]
    _ ≤ S ^ 40 := Nat.pow_le_pow_right hpos (by omega)

/-- INTERNAL: Bound the full work of one phase from its input rational-size
invariant, including work spent before a rejected draw or zero-count abort.
The input invariant is essential: arbitrary cursor rationals have unbounded
encoding lengths. No conclusion of phase_preserves_size is assumed here.
TEXLINE: main.tex:1348-1440 -/
theorem phase_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    otherSteps (boundedRunPhase r o₁ o₂ tape s j acc) ≤ (runSize n s) ^ 40 := by
  generalize hSdef : runSize n s = S at hacc ⊢
  have hparts : n ≤ S ∧ s.L ≤ S ∧ s.τ ≤ S ∧ s.restartCap ≤ S ∧
      s.observations ≤ S ∧ s.drawTrials ≤ S ∧ binaryRatLength s.ρ ≤ S := by
    rw [← hSdef]
    unfold runSize
    omega
  rcases hparts with ⟨hn, hL, hτ, hrestart, hobs, htrials, hρsize⟩
  have hS : 5 ≤ S := by
    have hρmin : 4 ≤ binaryRatLength s.ρ := by
      unfold binaryRatLength binaryNatLength
      omega
    rw [← hSdef]
    unfold runSize
    omega
  have hpos : 0 < S := by omega
  have hjS : j + 1 ≤ S := by omega
  have hjle : j ≤ S := by omega
  have hone : binaryRatLength (1 : ℚ) = 4 := by decide
  have h13 : S ≤ S ^ 3 := by
    simpa using Nat.pow_le_pow_right hpos (show 1 ≤ 3 by omega)
  have h03 : 1 ≤ S ^ 3 := by
    simpa using Nat.pow_le_pow_right hpos (show 0 ≤ 3 by omega)
  have hconstant : 9 ≤ S ^ 8 := by
    calc
      9 ≤ 5 ^ 8 := by norm_num
      _ ≤ S ^ 8 := Nat.pow_le_pow_left hS 8
  have hdom : 4 + S * (4 + S * S) ≤ S ^ 11 := by
    calc
      _ ≤ 9 * S ^ 3 := by nlinarith
      _ ≤ S ^ 8 * S ^ 3 := Nat.mul_le_mul_right _ hconstant
      _ = S ^ 11 := by rw [← pow_add]
  have hqbudget : binaryRatLength 1 + n *
      (binaryRatLength 1 + j * binaryRatLength s.ρ) ≤ S ^ 11 := by
    apply (show binaryRatLength 1 + n *
        (binaryRatLength 1 + j * binaryRatLength s.ρ) ≤
        4 + S * (4 + S * S) by rw [hone]; gcongr <;> first | assumption | omega).trans hdom
  have hlinear : (j + 1) * S ^ 10 ≤ S ^ 11 := by
    calc
      _ ≤ S * S ^ 10 := Nat.mul_le_mul_right _ hjS
      _ = S ^ 11 := by ring
  cases acc with
  | none => simp [boundedRunPhase, otherSteps]
  | some current =>
      rcases hacc current rfl with ⟨hweights, htables, hproduct⟩
      have hw : ∀ index, binaryRatLength (current.currentWeights index) ≤ S ^ 11 :=
        fun i => (hweights i).trans hlinear
      have ht : ∀ phase index, binaryRatLength (current.tables phase index) ≤ S ^ 11 :=
        fun p i => (htables p i).trans hlinear
      have hp : binaryRatLength current.product ≤ S ^ 11 := hproduct.trans hlinear
      let powerCost := S * (4 + S * S) ^ 2
      let restartCost := S * (2 * S + 3) + S *
        (1 + S * (4 + S * S) ^ 2 + (S * S * S + 1) +
          S * (S * (chainBudget S S (S ^ 11) + S * (4 * S + 3) + 3)))
      let observeCost := S * S + 1 + S *
        (1 + chainBudget S S (S ^ 11) +
          recordBudget S S (1 + S * (4 + S * S + 1)))
      let finishCost := S * S + 5 + 2 * (S + 4) + 4 * (S + 4) ^ 2 +
        2 * (phaseWorkSumBudget S + 3 * (S + 4)) ^ 2 +
        S * S * finishEntryBudget S (S + 4)
          (S ^ 11 + S * S * (4 * (S + 4)) + S * (4 * (S + 4)))
      let productCost := (S ^ 11 + phaseWorkSumBudget S + 3 * (S + 4)) ^ 2
      let extraCost := 2 + S * S * S + 1
      have hpower : otherSteps (ratPower s.ρ j) ≤ powerCost := by
        apply (ratPower_otherSteps_le s.ρ j).trans
        dsimp only [powerCost]
        rw [hone]
        gcongr <;> first | assumption | omega
      have hstart : otherSteps (restartPhase r o₁ o₂ tape s current.tables j
          current.bitCursor) ≤ restartCost := by
        apply (restartPhase_otherSteps_le r o₁ o₂ tape s current.tables j
          current.bitCursor (S ^ 11) hqbudget ht).trans
        dsimp only [restartCost]
        rw [hone]
        unfold chainBudget
        gcongr <;> first | assumption | omega
      have hq : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ j).val ≤ S ^ 11 := by
        have := ratPower_binary_length_le s.ρ j
        exact (Nat.add_le_add_left (Nat.mul_le_mul_left n this) _).trans hqbudget
      have hobserve (started : PairedSet n × ℕ) :
          otherSteps (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started) ≤ observeCost := by
        apply (observePhase_otherSteps_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started (S ^ 11) hq hw).trans
        dsimp only [observeCost]
        unfold chainBudget recordBudget
        gcongr <;> first | assumption | omega
      have hsum (started : PairedSet n × ℕ) (observed : ObservationCursor n)
          (ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started).val = some observed) :
          binaryRatLength observed.numeratorSum ≤ phaseWorkSumBudget S := by
        have hh := observePhase_height_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started observed ho
        have hb := binaryRatLength_le_height observed.numeratorSum
        apply (hb.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 2 hh) _)).trans
        unfold phaseWorkSumBudget
        rw [hone]
        gcongr <;> first | assumption | omega
      have hfinish (started : PairedSet n × ℕ) (observed : ObservationCursor n)
          (ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started).val = some observed) :
          otherSteps (finishPhase s j current.currentWeights observed) ≤ finishCost := by
        have hc := observePhase_counts_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started observed ho
        have hs := hsum started observed ho
        apply (finishPhase_otherSteps_le s j (S ^ 11) current.currentWeights
          observed hc hw).trans
        dsimp only [finishCost]
        unfold finishEntryBudget
        gcongr <;> first | assumption | omega
      have hmul (started : PairedSet n × ℕ) (observed : ObservationCursor n)
          (ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
            current.currentWeights started).val = some observed)
          (ratio : ℚ) (nextWeights : Multipliers n)
          (hf : (finishPhase s j current.currentWeights observed).val = some (ratio, nextWeights)) :
          otherSteps (ratMul current.product ratio) ≤ productCost := by
        have hc := observePhase_counts_le r o₁ o₂ tape s (ratPower s.ρ j).val
          current.currentWeights started observed ho
        have hs := hsum started observed ho
        have hr := finishPhase_ratio_length_le s j current.currentWeights observed
          (hc .transversal) ratio nextWeights hf
        apply (otherSteps_ratMul_le current.product ratio).trans
        dsimp only [productCost]
        apply Nat.pow_le_pow_left _ 2
        omega
      apply (show otherSteps (boundedRunPhase r o₁ o₂ tape s j (some current)) ≤
        phaseWorkBudget S from ?_).trans (phaseWorkBudget_le S hS)
      change otherSteps (boundedRunPhase r o₁ o₂ tape s j (some current)) ≤
        powerCost + restartCost + observeCost + finishCost + productCost + extraCost
      unfold boundedRunPhase
      rw [otherSteps_bind, otherSteps_bind]
      cases heStart : (restartPhase r o₁ o₂ tape s current.tables j current.bitCursor).val with
      | none => simp only [heStart, work_pure, Nat.add_zero]; omega
      | some started =>
          simp only [heStart]
          rw [otherSteps_bind]
          have hoCost := hobserve started
          cases heObs : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
              current.currentWeights started).val with
          | none => simp only [heObs, work_pure, Nat.add_zero]; omega
          | some observed =>
              simp only [heObs]
              rw [otherSteps_bind]
              have hfCost := hfinish started observed heObs
              cases heFinish : (finishPhase s j current.currentWeights observed).val with
              | none => simp only [heFinish, work_pure, Nat.add_zero]; omega
              | some finished =>
                  rcases finished with ⟨ratio, nextWeights⟩
                  have hmCost := hmul started observed heObs ratio nextWeights heFinish
                  simp only [heFinish, otherSteps_bind]
                  split
                  · simp only [otherSteps_bind, work_pure, Nat.add_zero, successor,
                      lessThan, learnedWeightWrite, work_word, work_words]
                    have htable : s.L * n * n + 1 ≤ S * S * S + 1 := by gcongr
                    dsimp only [extraCost]
                    omega
                  · simp only [work_pure, Nat.add_zero, successor, lessThan, work_word]
                    dsimp only [extraCost]
                    omega
end CountingMatroid.Analysis.BoundedRunPhase

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · closed phase_otherSteps_le using proved upstream chain/restart/observation/finishing work lemmas and an explicit polynomial envelope; the earlier extraction blocker is resolved.
* current · blocked · confirmed the upstream cost decomposition and unpacked the input size invariant; existing power/count/height support is downstream of this file, and the uniform-fold probe loses the reached-accumulator size bound. No new proof debt was introduced.
-/
