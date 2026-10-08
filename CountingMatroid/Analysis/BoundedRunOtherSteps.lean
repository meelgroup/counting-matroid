import CountingMatroid.Model.Program
import CountingMatroid.Analysis.RationalHeight
import CountingMatroid.Analysis.BoundedRunPhaseSize
import CountingMatroid.Analysis.BoundedRunPhaseWork

set_option autoImplicit false

/-!
The bounded-run nonoracle-work envelope is reduced to two single-phase
obligations: `phase_preserves_size` and `phase_otherSteps_le`. Their files
record the remaining multiplier-size and abort-path work proofs.

This module combines those statements by induction over the actual indexed
phase loop, bounds initialization, and proves the final-scaling work bound.
The full envelope is conditional on those two open child obligations; it is
not yet a completed resource proof. Existing power/count/height support is
still downstream in `BoundedRunResourceEnvelope` and needs upstream extraction
for use in the child proofs.
-/

namespace CountingMatroid.Analysis.BoundedRunOtherSteps
open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: Iterate the one-phase size invariant and cost bound together.
Keeping the phase index in the induction makes the cost hypothesis apply only
to reachable bounded-size cursors, including the absorbing aborted state.
TEXLINE: main.tex:1356-1440 -/
theorem phaseFold_work_and_size {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (hρ : 0 ≤ s.ρ) (k j : ℕ) (hj : j + k ≤ s.L)
    (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    let scan := Arlib.Computation.Charged.foldl
      (fun current index => boundedRunPhase r o₁ o₂ tape s index current)
      (List.range' j k) acc
    otherSteps scan ≤ k * (runSize n s) ^ 40 ∧
      PhaseSizeInvariant (runSize n s) (j + k) scan.val := by
  dsimp only
  induction k generalizing j acc with
  | zero => simpa [otherSteps] using hacc
  | succ k ih =>
      rw [List.range'_succ]
      change otherSteps (boundedRunPhase r o₁ o₂ tape s j acc >>= fun next =>
        Arlib.Computation.Charged.foldl
          (fun current index => boundedRunPhase r o₁ o₂ tape s index current)
          (List.range' (j + 1) k) next) ≤ _ ∧ _
      rw [otherSteps_bind]
      have hstep := phase_otherSteps_le r o₁ o₂ tape s hρ j (by omega) acc hacc
      have hnext := phase_preserves_size r o₁ o₂ tape s hρ j (by omega) acc hacc
      have htail := ih (j + 1) (by omega)
        (boundedRunPhase r o₁ o₂ tape s j acc).val hnext
      constructor
      · simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hstep htail.1
      · simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using htail.2

/-- INTERNAL: Final scaling costs polynomial work in the dimension and the
already-bounded product length. The logarithmic fold invariant avoids treating
the exponentially large integer scale as a unary size.
TEXLINE: main.tex:1376-1390 -/
theorem finalization_otherSteps_le {n : ℕ}
    (result : Option (AnnealingCursor n)) (K : ℕ)
    (hresult : ∀ current, result = some current → binaryRatLength current.product ≤ K) :
    otherSteps (match result with
      | none => pure ((0 : ℚ), (0 : ℕ))
      | some current => do
          let powerOfTwo ← natPower 2 n
          let scale ← ratOfNat powerOfTwo
          let estimate ← ratMul scale current.product
          pure (estimate, current.bitCursor)) ≤
      3 * n + 1 + (2 * n + 4 + K) ^ 2 := by
  cases result with
  | none => simp [otherSteps]
  | some current =>
      have hlogFold (l : List ℕ) (acc : ℕ) :
          (Arlib.Computation.Charged.foldl
            (fun value (_ : ℕ) => natMul value 2) l acc).val.log2 ≤
              acc.log2 + 2 * l.length := by
        induction l generalizing acc with
        | nil => simp
        | cons a l ih =>
            rw [Arlib.Computation.Charged.val_foldl_cons]
            have hmul := ScheduleOtherStepsEnvelope.log2_mul_le acc 2
            have htail := ih (acc * 2)
            simpa only [List.length_cons, natMul,
              Arlib.Computation.Charged.val_op] using
              (show (Arlib.Computation.Charged.foldl
                (fun value (_ : ℕ) => natMul value 2) l (acc * 2)).val.log2 ≤
                acc.log2 + 2 * (l.length + 1) by norm_num at hmul; omega)
      let a := (natPower 2 n).val
      have hlog : a.log2 ≤ 2 * n := by
        have hone : Nat.log2 1 = 0 := by decide
        simpa [a, natPower, Arlib.Computation.Charged.repeatFor, hone] using
          hlogFold (List.range n) 1
      have hcast : otherSteps (ratOfNat a) = a.log2 + 1 := by
        simp [otherSteps, ratOfNat, Arlib.Computation.Op.all,
          Arlib.Computation.CostVec.many]
      have hmul : otherSteps (ratMul (a : ℚ) current.product) ≤
          (binaryRatLength (a : ℚ) + binaryRatLength current.product) ^ 2 :=
        ScheduleOtherStepsEnvelope.rationalBinary_otherSteps_le .mul
          (a : ℚ) current.product ((a : ℚ) * current.product)
      rw [ScheduleOtherStepsEnvelope.binaryRatLength_natCast] at hmul
      have hp := hresult current rfl
      have hb : a.log2 + 4 + binaryRatLength current.product ≤ 2 * n + 4 + K := by
        omega
      have hm := hmul.trans (Nat.pow_le_pow_left hb 2)
      rw [otherSteps_bind, otherSteps_bind, otherSteps_bind]
      change otherSteps (natPower 2 n) +
        (otherSteps (ratOfNat a) + (otherSteps (ratMul (a : ℚ) current.product) + 0)) ≤ _
      rw [ScheduleOtherStepsEnvelope.natPower_otherSteps_eq, hcast]
      omega

/-- INTERNAL: Isolate the nonoracle-work conjunct of the run resource envelope.
The size includes every schedule field used to determine loop caps or rational
operands, and the bound includes all abort paths.
TEXLINE: main.tex:1348-1440 -/
theorem boundedRun_otherSteps_envelope :
    ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
      (s : AnnealingSchedule), 0 ≤ s.ρ →
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤
        100 * size ^ 100 := by
  intro n r o₁ o₂ tape s hρ
  let S := runSize n s
  have hS : 5 ≤ S := by
    dsimp [S, runSize, binaryRatLength, binaryNatLength]
    omega
  have hS1 : 1 ≤ S := by omega
  have hn : n ≤ S := by dsimp [S, runSize]; omega
  have hL : s.L ≤ S := by dsimp [S, runSize]; omega
  have hL1 : s.L + 1 ≤ S := by dsimp [S, runSize]; omega
  have h6 : 6 ≤ S ^ 10 := by
    have h := Nat.pow_le_pow_left hS 10
    norm_num at h
    omega
  let initial : AnnealingCursor n :=
    ⟨(allocateLearnedWeights n s.L (initialWeights n).val).val,
      (initialWeights n).val, 1, 0⟩
  have hinit : PhaseSizeInvariant S 0 (some initial) := by
    intro current hcurrent
    cases Option.some.inj hcurrent
    dsimp [initial, initialWeights, allocateLearnedWeights]
    simp only [Nat.one_mul]
    change (∀ _ : DefectIndex n, binaryRatLength (4 : ℚ) ≤ S ^ 10) ∧
      (∀ (_ : ℕ) (_ : DefectIndex n), binaryRatLength (4 : ℚ) ≤ S ^ 10) ∧
      binaryRatLength (1 : ℚ) ≤ S ^ 10
    have hfour : binaryRatLength (4 : ℚ) = 6 := by decide
    have hone : binaryRatLength (1 : ℚ) = 4 := by decide
    rw [hfour, hone]
    exact ⟨fun _ => h6, fun _ _ => h6, by omega⟩
  let scan := Arlib.Computation.Charged.repeatFor
    (boundedRunPhase r o₁ o₂ tape s) s.L (some initial)
  have hscan : otherSteps scan ≤ s.L * S ^ 40 ∧
      PhaseSizeInvariant S s.L scan.val := by
    simpa [scan, Arlib.Computation.Charged.repeatFor, List.range_eq_range'] using
      phaseFold_work_and_size r o₁ o₂ tape s hρ s.L 0 (by omega) (some initial) hinit
  have hprod : ∀ current, scan.val = some current →
      binaryRatLength current.product ≤ S ^ 11 := by
    intro current hc
    have hp := (hscan.2 current hc).2.2
    calc
      binaryRatLength current.product ≤ (s.L + 1) * S ^ 10 := hp
      _ ≤ S * S ^ 10 := Nat.mul_le_mul_right _ hL1
      _ = S ^ 11 := by ring
  have hfinal := finalization_otherSteps_le scan.val (S ^ 11) hprod
  have hpow (k : ℕ) (hk : k ≤ 100) : S ^ k ≤ S ^ 100 :=
    Nat.pow_le_pow_right hS1 hk
  have hquad : n * n + 1 ≤ 2 * S ^ 2 := by
    have hnn := Nat.mul_le_mul hn hn
    have hone : 1 ≤ S ^ 2 := one_le_pow₀ hS1
    nlinarith only [hnn, hone]
  have hi : n * n + 1 ≤ 2 * S ^ 100 :=
    hquad.trans (Nat.mul_le_mul_left 2 (hpow 2 (by omega)))
  have ha : s.L * (n * n + 1) ≤ 2 * S ^ 100 := by
    calc
      s.L * (n * n + 1) ≤ S * (2 * S ^ 2) := Nat.mul_le_mul hL hquad
      _ = 2 * S ^ 3 := by ring
      _ ≤ 2 * S ^ 100 := Nat.mul_le_mul_left 2 (hpow 3 (by omega))
  have hs : otherSteps scan ≤ S ^ 100 := by
    calc
      otherSteps scan ≤ s.L * S ^ 40 := hscan.1
      _ ≤ S * S ^ 40 := Nat.mul_le_mul_right _ hL
      _ = S ^ 41 := by ring
      _ ≤ S ^ 100 := hpow 41 (by omega)
  have hf : 3 * n + 1 + (2 * n + 4 + S ^ 11) ^ 2 ≤ 53 * S ^ 100 := by
    have h11 : S ≤ S ^ 11 := Nat.le_self_pow (by decide) S
    have h22 : S ≤ S ^ 22 := Nat.le_self_pow (by decide) S
    have hone : 1 ≤ S ^ 11 := one_le_pow₀ hS1
    have hb : 2 * n + 4 + S ^ 11 ≤ 7 * S ^ 11 := by omega
    have hsq := Nat.pow_le_pow_left hb 2
    have heq : (7 * S ^ 11) ^ 2 = 49 * S ^ 22 := by ring
    rw [heq] at hsq
    calc
      3 * n + 1 + (2 * n + 4 + S ^ 11) ^ 2 ≤ 53 * S ^ 22 := by omega
      _ ≤ 53 * S ^ 100 := Nat.mul_le_mul_left 53 (hpow 22 (by omega))
  have hiCost : otherSteps (initialWeights n) = n * n + 1 := by
    simp [otherSteps, initialWeights, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  have haCost : otherSteps (allocateLearnedWeights n s.L (initialWeights n).val) =
      s.L * (n * n + 1) := by
    simp [otherSteps, allocateLearnedWeights, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  change otherSteps (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤ 100 * S ^ 100
  unfold CountingMatroid.Program.boundedRun
  rw [otherSteps_bind, otherSteps_bind, otherSteps_bind]
  change otherSteps (initialWeights n) +
    (otherSteps (allocateLearnedWeights n s.L (initialWeights n).val) +
      (otherSteps scan + otherSteps (match scan.val with
        | none => pure ((0 : ℚ), (0 : ℕ))
        | some current => do
            let powerOfTwo ← natPower 2 n
            let scale ← ratOfNat powerOfTwo
            let estimate ← ratMul scale current.product
            pure (estimate, current.bitCursor)))) ≤ 100 * S ^ 100
  rw [hiCost, haCost]
  omega

end CountingMatroid.Analysis.BoundedRunOtherSteps

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · decomposed · combined indexed phase-size preservation and phase work bounds by induction; proved final-scaling work using a logarithmic integer-fold invariant; prepared the two independent phase obligations for live handoff.

* r17 · blocked · checked the three-bind charge decomposition; identified existing power/count/height prerequisites behind the downstream import and requested their mechanical extraction, without adding helper proof debt.
* r16 · open handoff · unfolding boundedRun and rewriting otherSteps_bind exposes the phase-loop charge; a reachable multiplier-and-work invariant remains required, including rejected draws and failed finishPhase scans.
-/
