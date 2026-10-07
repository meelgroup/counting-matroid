import CountingMatroid.Model.Run
import CountingMatroid.Analysis.EstimateMedianResource

set_option autoImplicit false

namespace CountingMatroid.Analysis.LeastHalvingsCost

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: The exact encoding length of a halving accumulator.
TEXLINE: main.tex:1348-1351 -/
private theorem halfPower_binaryRatLength (i : ℕ) :
    binaryRatLength ((1 / 2 : ℚ) ^ i) = i + 4 := by
  have hn : (1 / 2 : ℚ).num = 1 := by norm_num
  have hd : (1 / 2 : ℚ).den = 2 := by norm_num
  unfold binaryRatLength binaryNatLength
  rw [Rat.num_pow, Rat.den_pow, hn, hd, Nat.log2_two_pow]
  norm_num
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega

/-- INTERNAL: The capped halving search has polynomial charged work in its
input rational encoding and denominator cap. The loop's rational accumulator
is a power of one half, so its encoding grows by at most one bit per round.
TEXLINE: main.tex:1348-1351 -/
theorem leastHalvings_otherSteps_le (q : ℚ) :
    otherSteps (CountingMatroid.Program.leastHalvings q) ≤
      100 * (q.den.log2 + 8) *
        (binaryRatLength q + q.den.log2 + 16) ^ 2 + 1 := by
  have hdiv (p : ℚ) : otherSteps (ratDiv p 2) ≤ (binaryRatLength p + 4) ^ 2 := by
    simp only [otherSteps, ratDiv, Arlib.Computation.Charged.cost_opMany]
    simp [Arlib.Computation.Op.all, Arlib.Computation.CostVec.many,
      binaryRatLength, binaryNatLength]
    change (p.num.natAbs.log2 + p.den.log2 + 3 + 4) ^ 2 ≤ _
    exact Nat.pow_le_pow_left (by omega) 2
  let N := q.den.log2 + 8
  let K := binaryRatLength q + q.den.log2 + 16
  let step : (ℕ × ℚ) → ℕ → Arlib.Computation.Charged Op Cell (Option (ℕ × ℚ)) :=
    fun acc _ => do
      let needsStep ← ratLess q acc.2
      if needsStep then
        let b ← successor acc.1
        let power ← ratDiv acc.2 2
        pure (some (b, power))
      else pure none
  have hstep_val (acc : ℕ × ℚ) (i : ℕ) :
      (step acc i).val =
        if q < acc.2 then some (acc.1 + 1, acc.2 / 2) else none := by
    by_cases h : q < acc.2 <;>
      simp [step, ratLess, h, successor, ratDiv]
  have hstep_cost (b i : ℕ) (hb : b ≤ N) :
      otherSteps (step (b, (1 / 2 : ℚ) ^ b) i) ≤ 3 * K ^ 2 := by
    have hless := ratLess_otherSteps_le q ((1 / 2 : ℚ) ^ b)
    have hd := hdiv ((1 / 2 : ℚ) ^ b)
    rw [halfPower_binaryRatLength] at hless hd
    have hK : 1 ≤ K := by dsimp [K]; omega
    have hlen : binaryRatLength q + (b + 4) ≤ K := by
      dsimp [N, K] at hb ⊢
      omega
    have hdivlen : b + 8 ≤ K := by
      dsimp [N, K] at hb ⊢
      omega
    have hdivcost : otherSteps (ratDiv ((1 / 2 : ℚ) ^ b) 2) ≤ K ^ 2 :=
      hd.trans (Nat.pow_le_pow_left hdivlen 2)
    have hlesscost : otherSteps (ratLess q ((1 / 2 : ℚ) ^ b)) ≤ K :=
      hless.trans hlen
    by_cases h : q < (1 / 2 : ℚ) ^ b
    · have heq : otherSteps (step (b, (1 / 2 : ℚ) ^ b) i) =
          otherSteps (ratLess q ((1 / 2 : ℚ) ^ b)) + 1 +
            otherSteps (ratDiv ((1 / 2 : ℚ) ^ b) 2) := by
        simp only [step, otherSteps_bind, ratLess, h]
        simp [otherSteps, successor, ratDiv, Arlib.Computation.Op.all,
          Arlib.Computation.CostVec.many]
        omega
      rw [heq]
      nlinarith
    · have heq : otherSteps (step (b, (1 / 2 : ℚ) ^ b) i) =
          otherSteps (ratLess q ((1 / 2 : ℚ) ^ b)) := by
        simp only [step, otherSteps_bind, ratLess, h]
        simp [otherSteps, Arlib.Computation.Op.all]
      rw [heq]
      nlinarith
  have hfoldcost {β ι : Type}
      (f : β → ι → Arlib.Computation.Charged Op Cell (Option β))
      (i : ι) (l : List ι) (b : β) :
      otherSteps (Arlib.Computation.Charged.foldlWhile f (i :: l) b) =
        otherSteps (f b i) +
          match (f b i).val with
          | none => 0
          | some b' => otherSteps (Arlib.Computation.Charged.foldlWhile f l b') := by
    cases h : (f b i).val with
    | none =>
        have hv := h
        simp only [Arlib.Computation.Charged.val] at hv
        simp only [Arlib.Computation.Charged.foldlWhile, hv, otherSteps,
          Arlib.Computation.Charged.cost]
        omega
    | some b' =>
        have hv := h
        simp only [Arlib.Computation.Charged.val] at hv
        simp only [Arlib.Computation.Charged.foldlWhile, hv, otherSteps,
          Arlib.Computation.Charged.cost, Pi.add_apply]
        have hadd := foldl_word_add Arlib.Computation.Op.all
          (fun x => (f b i).cost (Op.word x))
          (fun x => (Arlib.Computation.Charged.foldlWhile f l b').cost (Op.word x)) 0 0
        simp only [Nat.zero_add] at hadd
        simp only [Arlib.Computation.Charged.cost] at hadd
        rw [hadd]
        omega
  have hloop : ∀ (l : List ℕ) (b : ℕ), b + l.length ≤ N →
      otherSteps (Arlib.Computation.Charged.foldlWhile
        (fun acc i => step acc i) l (b, (1 / 2 : ℚ) ^ b)) ≤
        l.length * (3 * K ^ 2) := by
    intro l
    induction l with
    | nil =>
        intro b hb
        simp [otherSteps, Arlib.Computation.Charged.foldlWhile,
          Arlib.Computation.Charged.cost, Arlib.Computation.Op.all]
    | cons i l ih =>
        intro b hb
        have hfirst := hstep_cost b i (by simp [N] at hb ⊢; omega)
        by_cases h : q < (1 / 2 : ℚ) ^ b
        · have hs : (step (b, (1 / 2 : ℚ) ^ b) i).val =
              some (b + 1, (1 / 2 : ℚ) ^ (b + 1)) := by
            rw [hstep_val (b, (1 / 2 : ℚ) ^ b) i, if_pos h]
            rw [pow_succ]
            simp [div_eq_mul_inv]
          have htail := ih (b + 1) (by simp only [List.length_cons] at hb; omega)
          rw [hfoldcost, hs]
          simp only [List.length_cons]
          rw [show (l.length + 1) * (3 * K ^ 2) =
            3 * K ^ 2 + l.length * (3 * K ^ 2) by ring]
          omega
        · have hs : (step (b, (1 / 2 : ℚ) ^ b) i).val = none := by
            rw [hstep_val (b, (1 / 2 : ℚ) ^ b) i, if_neg h]
          rw [hfoldcost, hs]
          simp only [List.length_cons]
          rw [show (l.length + 1) * (3 * K ^ 2) =
            3 * K ^ 2 + l.length * (3 * K ^ 2) by ring]
          omega
  have hrun := hloop (List.range N) 0 (by simp [N])
  have hcap : otherSteps (binaryLoopBound q.den) = 1 := by
    simp [binaryLoopBound, otherSteps, Arlib.Computation.Op.all]
  have hpure (n : ℕ) :
      otherSteps (pure n : Arlib.Computation.Charged Op Cell ℕ) = 0 := by
    simp [otherSteps, Arlib.Computation.Op.all]
  unfold CountingMatroid.Program.leastHalvings
  simp only [otherSteps_bind, Arlib.Computation.Charged.repeatWhile]
  rw [hcap]
  simp only [hpure, Nat.add_zero]
  simp only [binaryLoopBound, Arlib.Computation.Charged.val_op]
  change 1 + otherSteps (Arlib.Computation.Charged.foldlWhile
    (fun acc i => step acc i) (List.range N) (0, (1 : ℚ))) ≤
      100 * N * K ^ 2 + 1
  have hrun' : otherSteps (Arlib.Computation.Charged.foldlWhile
      (fun acc i => step acc i) (List.range N) (0, (1 : ℚ))) ≤
      N * (3 * K ^ 2) := by
    simpa only [List.length_range, pow_zero] using hrun
  have hpoly : N * (3 * K ^ 2) ≤ 100 * N * K ^ 2 := by
    calc
      N * (3 * K ^ 2) = 3 * (N * K ^ 2) := by ring
      _ ≤ 100 * (N * K ^ 2) := Nat.mul_le_mul_right _ (by decide)
      _ = 100 * N * K ^ 2 := by ring
  omega

end CountingMatroid.Analysis.LeastHalvingsCost

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r12 · proved · bounded each halving step and summed the charged fold using
  the power-of-one-half accumulator invariant.
* r11 · partial · proved the exact rational encoding length of a halving
  accumulator; the charged fold bound still needs the state invariant and sum.
-/
