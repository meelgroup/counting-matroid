import CountingMatroid.Model.Run
import CountingMatroid.Analysis.LeastHalvingsCost
import CountingMatroid.Analysis.ScheduleOpeningCost
import CountingMatroid.Analysis.ScheduleThermalSetupCost

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The nonoracle charge is additive under charged sequencing. -/
private theorem otherSteps_bind {α β : Type}
    (q : Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell α)
    (f : α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell β) :
    otherSteps (q >>= f) = otherSteps q + otherSteps (f q.val) := by
  have fold_add (l : List Arlib.Computation.Op)
      (u v : Arlib.Computation.Op → ℕ) (a b : ℕ) :
      l.foldl (fun z x => z + (u x + v x)) (a + b) =
        l.foldl (fun z x => z + u x) a +
          l.foldl (fun z x => z + v x) b := by
    induction l generalizing a b with
    | nil => rfl
    | cons x xs ih =>
        simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (a + u x) (b + v x)
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := fold_add Arlib.Computation.Op.all
    (fun x => q.cost (CountingMatroid.Model.Operations.Op.word x))
    (fun x => (f q.val).cost (CountingMatroid.Model.Operations.Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega

/-- INTERNAL: A charged loop that may stop early costs at most its cap times
the cost of one round. -/
theorem otherSteps_foldlWhile_le {α β : Type}
    (f : β → α → Arlib.Computation.Charged
      CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell (Option β))
    (l : List α) (b : β) (k : ℕ)
    (h : ∀ b a, otherSteps (f b a) ≤ k) :
    otherSteps (Arlib.Computation.Charged.foldlWhile f l b) ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp [otherSteps]
  | cons a l ih =>
      cases hv : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at hv
          have heq : otherSteps (Arlib.Computation.Charged.foldlWhile f (a :: l) b) =
              otherSteps (f b a) := by
            simp [otherSteps, Arlib.Computation.Charged.foldlWhile, hv,
              Arlib.Computation.Charged.cost]
          rw [heq]
          calc otherSteps (f b a) ≤ k := h b a
            _ ≤ (a :: l).length * k := by
              simpa [List.length_cons] using
                (Nat.le_mul_of_pos_left k (Nat.succ_pos l.length))
      | some b' =>
          simp only [Arlib.Computation.Charged.val] at hv
          have hcost : (Arlib.Computation.Charged.foldlWhile f (a :: l) b).cost =
              (f b a).cost + (Arlib.Computation.Charged.foldlWhile f l b').cost := by
            simp [Arlib.Computation.Charged.foldlWhile, hv,
              Arlib.Computation.Charged.cost]
          have heq : otherSteps (Arlib.Computation.Charged.foldlWhile f (a :: l) b) =
              otherSteps (f b a) +
                otherSteps (Arlib.Computation.Charged.foldlWhile f l b') := by
            calc
              otherSteps (Arlib.Computation.Charged.foldlWhile f (a :: l) b) =
                  otherSteps ((f b a) >>= fun _ =>
                    Arlib.Computation.Charged.foldlWhile f l b') := by
                    simp only [otherSteps, hcost, Arlib.Computation.Charged.cost_bind,
                      Pi.add_apply]
              _ = _ := by rw [otherSteps_bind]
          rw [heq]
          have htail := ih b'
          have hhead := h b a
          simpa [List.length_cons, Nat.succ_mul, Nat.add_comm, Nat.add_left_comm,
            Nat.add_assoc] using Nat.add_le_add hhead htail

/-- INTERNAL: A stopped loop that increments its first counter at most once
per round never exceeds its cap. -/
theorem foldlWhile_first_le {α γ : Type}
    (f : (ℕ × γ) → α → Arlib.Computation.Charged
      CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
      (Option (ℕ × γ))) (l : List α) (b : ℕ × γ)
    (h : ∀ b a b', (f b a).val = some b' → b'.1 ≤ b.1 + 1) :
    (Arlib.Computation.Charged.foldlWhile f l b).val.1 ≤ b.1 + l.length := by
  induction l generalizing b with
  | nil => simp [Arlib.Computation.Charged.foldlWhile,
      Arlib.Computation.Charged.val]
  | cons a l ih =>
      cases hv : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at hv
          simp [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val, hv]
      | some b' =>
          have hfirst := h b a b' hv
          have hrest := ih b'
          simp only [Arlib.Computation.Charged.val] at hv
          simp only [Arlib.Computation.Charged.foldlWhile,
            Arlib.Computation.Charged.val, hv]
          simp only [Arlib.Computation.Charged.val] at hrest ⊢
          simp only [List.length_cons]
          omega

/-- INTERNAL: The halving counter cannot exceed the length of its capped search.
TEXLINE: main.tex:1348-1351 -/
theorem leastHalvings_value_le (q : ℚ) :
    (CountingMatroid.Program.leastHalvings q).val ≤ q.den.log2 + 8 := by
  have hstep (acc : ℕ × ℚ) (round : ℕ) (next : ℕ × ℚ) :
      (do
        let needsStep ← CountingMatroid.Model.Operations.ratLess q acc.2
        if needsStep then
          let b ← CountingMatroid.Model.Operations.successor acc.1
          let power ← CountingMatroid.Model.Operations.ratDiv acc.2 2
          pure (some (b, power))
        else pure none : Arlib.Computation.Charged
          CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
          (Option (ℕ × ℚ))).val = some next → next.1 ≤ acc.1 + 1 := by
    by_cases h : q < acc.2
    · simp [CountingMatroid.Model.Operations.ratLess,
        CountingMatroid.Model.Operations.successor,
        CountingMatroid.Model.Operations.ratDiv, h]
      intro heq
      cases heq
      omega
    · simp [CountingMatroid.Model.Operations.ratLess, h]
  have hloop := foldlWhile_first_le
    (fun acc (_ : ℕ) => do
      let needsStep ← CountingMatroid.Model.Operations.ratLess q acc.2
      if needsStep then
        let b ← CountingMatroid.Model.Operations.successor acc.1
        let power ← CountingMatroid.Model.Operations.ratDiv acc.2 2
        pure (some (b, power))
      else pure none)
    (List.range (q.den.log2 + 8)) (0, (1 : ℚ))
    (fun acc round next => hstep acc round next)
  simpa [CountingMatroid.Program.leastHalvings,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.repeatWhile] using hloop

/-- INTERNAL: A product's binary length is at most the sum of the factor
lengths, with one carry bit. -/
theorem log2_mul_le (a b : ℕ) :
    (a * b).log2 ≤ a.log2 + b.log2 + 1 := by
  simp only [Nat.log2_eq_log_two]
  by_cases ha : a = 0
  · simp [ha]
  by_cases hb : b = 0
  · simp [hb]
  have ha' : a < 2 ^ (Nat.log 2 a + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two a
  have hb' : b < 2 ^ (Nat.log 2 b + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two b
  have hp : a * b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    calc
      a * b < 2 ^ (Nat.log 2 a + 1) * b := Nat.mul_lt_mul_of_pos_right ha' (Nat.pos_of_ne_zero hb)
      _ ≤ 2 ^ (Nat.log 2 a + 1) * 2 ^ (Nat.log 2 b + 1) :=
        Nat.mul_le_mul_left _ hb'.le
      _ = 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by ring
  have hlog := (Nat.log_lt_iff_lt_pow Nat.one_lt_two (Nat.mul_ne_zero ha hb)).2 hp
  omega

/-- INTERNAL: A sum's binary length is bounded by the lengths of its terms
plus one carry bit. -/
theorem log2_add_le (a b : ℕ) :
    (a + b).log2 ≤ a.log2 + b.log2 + 1 := by
  simp only [Nat.log2_eq_log_two]
  by_cases hab : a + b = 0
  · simp [hab]
  have ha' : a < 2 ^ (Nat.log 2 a + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two a
  have hb' : b < 2 ^ (Nat.log 2 b + 1) := by
    simpa only [Nat.succ_eq_add_one] using Nat.lt_pow_succ_log_self Nat.one_lt_two b
  have haBound : 2 ^ (Nat.log 2 a + 1) ≤
      2 ^ (Nat.log 2 a + Nat.log 2 b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hbBound : 2 ^ (Nat.log 2 b + 1) ≤
      2 ^ (Nat.log 2 a + Nat.log 2 b + 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  have hp : a + b < 2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by
    have hpow : 2 * 2 ^ (Nat.log 2 a + Nat.log 2 b + 1) =
        2 ^ (Nat.log 2 a + Nat.log 2 b + 2) := by ring
    rw [← hpow]
    omega
  have hlog := (Nat.log_lt_iff_lt_pow Nat.one_lt_two hab).2 hp
  omega

/-- INTERNAL: Multiplying two reduced rational numbers adds at most their
binary encoding lengths. -/
theorem binaryRatLength_mul_le (q s : ℚ) :
    binaryRatLength (q * s) ≤ binaryRatLength q + binaryRatLength s := by
  have hg : 0 < (q.num * s.num).natAbs.gcd (q.den * s.den) :=
    Nat.gcd_pos_of_pos_right _ (Nat.mul_pos q.den_pos s.den_pos)
  simp only [Int.natAbs_mul] at hg
  have hnumEq := congrArg Int.natAbs (Rat.num_mul_num_eq_num_mul_gcd q s)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hnumEq
  have hnum : (q * s).num.natAbs ≤ q.num.natAbs * s.num.natAbs := by
    calc
      (q * s).num.natAbs ≤ (q * s).num.natAbs *
          (q.num.natAbs * s.num.natAbs).gcd (q.den * s.den) :=
        Nat.le_mul_of_pos_right _ hg
      _ = q.num.natAbs * s.num.natAbs := hnumEq.symm
  have hden : (q * s).den ≤ q.den * s.den :=
    Nat.le_of_dvd (Nat.mul_pos q.den_pos s.den_pos) (Rat.mul_den_dvd q s)
  have hnlog : (q * s).num.natAbs.log2 ≤
      q.num.natAbs.log2 + s.num.natAbs.log2 + 1 := by
    have hm := log2_mul_le q.num.natAbs s.num.natAbs
    simp only [Nat.log2_eq_log_two] at hm ⊢
    exact (Nat.log_mono_right (b := 2) hnum).trans hm
  have hdlog : (q * s).den.log2 ≤ q.den.log2 + s.den.log2 + 1 := by
    have hm := log2_mul_le q.den s.den
    simp only [Nat.log2_eq_log_two] at hm ⊢
    exact (Nat.log_mono_right (b := 2) hden).trans hm
  unfold binaryRatLength binaryNatLength
  omega

/-- INTERNAL: Rational inversion swaps numerator and denominator lengths. -/
theorem binaryRatLength_inv_eq (q : ℚ) :
    binaryRatLength q⁻¹ = binaryRatLength q := by
  by_cases hz : q.num = 0
  · have hq : q = 0 := Rat.zero_of_num_zero hz
    simp [hq]
  · unfold binaryRatLength binaryNatLength
    simp [Rat.num_inv, Rat.den_inv, Int.natAbs_mul,
      Int.natAbs_sign, hz, Int.natAbs_natCast]
    omega

/-- INTERNAL: Rational division adds no more binary encoding length than
multiplication by the denominator's reciprocal. -/
theorem binaryRatLength_div_le (q s : ℚ) :
    binaryRatLength (q / s) ≤ binaryRatLength q + binaryRatLength s := by
  rw [div_eq_mul_inv]
  simpa only [binaryRatLength_inv_eq] using binaryRatLength_mul_le q s⁻¹

/-- INTERNAL: A charged rational binary operation is bounded by its input encodings. -/
theorem rationalBinary_otherSteps_le (instr : Arlib.Computation.Op)
    (a b result : ℚ) :
    otherSteps (Arlib.Computation.Charged.opMany
      (CountingMatroid.Model.Operations.Op.word instr)
      ((a.num.natAbs.log2 + a.den.log2 + 3 +
        (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2) result) ≤
      (binaryRatLength a + binaryRatLength b) ^ 2 := by
  have hcost (z : ℕ) : otherSteps
      (Arlib.Computation.Charged.opMany
        (CountingMatroid.Model.Operations.Op.word instr) z result) = z := by
    cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  rw [hcost]
  unfold binaryRatLength binaryNatLength
  apply Nat.pow_le_pow_left
  omega

/-- INTERNAL: The nonnegative ceiling of a reduced rational is at most the
absolute value of its numerator. -/
theorem rationalCeil_value_le_num (q : ℚ) :
    (CountingMatroid.Model.Operations.rationalCeil q).val ≤ q.num.natAbs := by
  change Int.toNat q.ceil ≤ q.num.natAbs
  rw [Int.toNat_le]
  apply Rat.ceil_le_iff.mpr
  by_cases hq : 0 ≤ q
  · have hd : (1 : ℚ) ≤ (q.den : ℚ) := by exact_mod_cast q.den_pos
    calc
      q = q * 1 := by ring
      _ ≤ q * (q.den : ℚ) := mul_le_mul_of_nonneg_left hd hq
      _ = (q.num : ℚ) := Rat.mul_den_eq_num q
      _ ≤ (q.num.natAbs : ℚ) := by
        calc
          (q.num : ℚ) ≤ |(q.num : ℚ)| := le_abs_self _
          _ = (q.num.natAbs : ℚ) := by
            rw [← Int.cast_abs, ← Nat.cast_natAbs]
  · have : q ≤ 0 := le_of_lt (lt_of_not_ge hq)
    exact this.trans (by positivity)

/-- INTERNAL: A natural cast needs its own binary length plus three framing bits. -/
theorem binaryRatLength_natCast (a : ℕ) :
    binaryRatLength (a : ℚ) = a.log2 + 4 := by
  simp only [binaryRatLength, binaryNatLength, Rat.num_natCast,
    Rat.den_natCast, Int.natAbs_natCast]
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega

/-- INTERNAL: A rational ceiling's binary logarithm fits within the rational
operand's encoding length. -/
theorem rationalCeil_log2_le (q : ℚ) :
    ((CountingMatroid.Model.Operations.rationalCeil q).val).log2 ≤
      binaryRatLength q := by
  have h := Nat.log_mono_right (b := 2) (rationalCeil_value_le_num q)
  rw [← Nat.log2_eq_log_two, ← Nat.log2_eq_log_two] at h
  unfold binaryRatLength binaryNatLength
  omega

/-- INTERNAL: The schedule's observation quotient has encoding length
controlled by the numerator and the encoded accuracy and denominator.
TEXLINE: main.tex:1348-1360 -/
theorem observationQuotient_length_le (a b : ℕ) (q : ℚ) :
    binaryRatLength ((a : ℚ) / ((q / (b : ℚ)) * (q / (b : ℚ)))) ≤
      a.log2 + 2 * binaryRatLength q + 2 * b.log2 + 12 := by
  have hdiv := binaryRatLength_div_le q (b : ℚ)
  have hmul := binaryRatLength_mul_le (q / (b : ℚ)) (q / (b : ℚ))
  have hquot := binaryRatLength_div_le (a : ℚ)
    ((q / (b : ℚ)) * (q / (b : ℚ)))
  rw [binaryRatLength_natCast] at hdiv hquot
  omega

/-- INTERNAL: Each multiplication in a charged natural power costs one word step. -/
theorem natPower_otherSteps_eq (base exponent : ℕ) :
    otherSteps (CountingMatroid.Program.natPower base exponent) = exponent := by
  have hfold (l : List ℕ) (acc : ℕ) :
      otherSteps (Arlib.Computation.Charged.foldl
        (fun acc _ => CountingMatroid.Model.Operations.natMul acc base) l acc) =
        l.length := by
    induction l generalizing acc with
    | nil => simp [otherSteps]
    | cons x xs ih =>
        rw [show Arlib.Computation.Charged.foldl
          (fun acc _ => CountingMatroid.Model.Operations.natMul acc base)
          (x :: xs) acc =
          CountingMatroid.Model.Operations.natMul acc base >>= fun next =>
            Arlib.Computation.Charged.foldl
              (fun acc _ => CountingMatroid.Model.Operations.natMul acc base)
              xs next from rfl, otherSteps_bind]
        have hone : otherSteps (CountingMatroid.Model.Operations.natMul acc base) = 1 := by
          simp [otherSteps, CountingMatroid.Model.Operations.natMul,
            Arlib.Computation.CostVec.one, Arlib.Computation.Op.all]
        rw [hone, ih]
        simp only [List.length_cons]
        omega
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using hfold (List.range exponent) 1

/-- INTERNAL: The capped search for rejection-draw width charges at most three
word operations per permitted round.
TEXLINE: main.tex:1392-1421 -/
theorem leastDrawTrials_otherSteps_le (M : ℕ) :
    otherSteps (CountingMatroid.Program.leastDrawTrials M) ≤
      3 * (M.log2 + 8) + 2 := by
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [otherSteps_bind]
  have hstep (round : ℕ) (acc : ℕ × ℕ) :
      otherSteps (do
        let needsStep ← CountingMatroid.Model.Operations.lessThan acc.2 (32 * M)
        if needsStep then
          let d ← CountingMatroid.Model.Operations.successor acc.1
          let power ← CountingMatroid.Model.Operations.natMul acc.2 2
          pure (some (d, power))
        else pure none) ≤ 3 := by
    by_cases h : acc.2 < 32 * M
    · simp [CountingMatroid.Model.Operations.lessThan,
        CountingMatroid.Model.Operations.successor,
        CountingMatroid.Model.Operations.natMul, h, otherSteps,
        Arlib.Computation.Op.all]
    · simp [CountingMatroid.Model.Operations.lessThan,
        CountingMatroid.Model.Operations.successor,
        CountingMatroid.Model.Operations.natMul, h, otherSteps,
        Arlib.Computation.Op.all]
  have hloop := otherSteps_foldlWhile_le
    (fun acc (_ : ℕ) => do
      let needsStep ← CountingMatroid.Model.Operations.lessThan acc.2 (32 * M)
      if needsStep then
        let d ← CountingMatroid.Model.Operations.successor acc.1
        let power ← CountingMatroid.Model.Operations.natMul acc.2 2
        pure (some (d, power))
      else pure none)
    (List.range (M.log2 + 8)) (1, 2) 3 (fun acc round => hstep round acc)
  -- The loop cap and target are supplied by one charged primitive each.
  have hloop' : otherSteps (Arlib.Computation.Charged.repeatWhile
      (fun _ acc => do
        let needsStep ← CountingMatroid.Model.Operations.lessThan acc.2 (32 * M)
        if needsStep then
          let d ← CountingMatroid.Model.Operations.successor acc.1
          let power ← CountingMatroid.Model.Operations.natMul acc.2 2
          pure (some (d, power))
        else pure none) (M.log2 + 8) (1, 2)) ≤ 3 * (M.log2 + 8) := by
    simpa [Arlib.Computation.Charged.repeatWhile, Nat.mul_comm] using hloop
  have hcap : otherSteps (CountingMatroid.Model.Operations.binaryLoopBound M) = 1 := by
    simp [otherSteps, CountingMatroid.Model.Operations.binaryLoopBound,
      Arlib.Computation.Op.all]
  have hmul : otherSteps (CountingMatroid.Model.Operations.natMul 32 M) = 1 := by
    simp [otherSteps, CountingMatroid.Model.Operations.natMul,
      Arlib.Computation.Op.all]
  have hpure (a : ℕ) : otherSteps
      (pure a : Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
        CountingMatroid.Model.Operations.Cell ℕ) = 0 := by
    simp [otherSteps]
  simp only [hcap, hmul, hpure]
  change 1 + (1 + otherSteps (Arlib.Computation.Charged.repeatWhile
      (fun _ acc => do
        let needsStep ← CountingMatroid.Model.Operations.lessThan acc.2 (32 * M)
        if needsStep then
          let d ← CountingMatroid.Model.Operations.successor acc.1
          let power ← CountingMatroid.Model.Operations.natMul acc.2 2
          pure (some (d, power))
        else pure none) (M.log2 + 8) (1, 2))) ≤ 3 * (M.log2 + 8) + 2
  omega

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
