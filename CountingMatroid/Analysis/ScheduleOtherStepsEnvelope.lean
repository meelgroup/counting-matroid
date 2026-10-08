import CountingMatroid.Model.Run
import CountingMatroid.Analysis.LeastHalvingsCost
import CountingMatroid.Analysis.ScheduleOpeningCost
import CountingMatroid.Analysis.ScheduleThermalSetupCost
import CountingMatroid.Analysis.ScheduleThermalRestCost

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
private theorem rationalBinary_otherSteps_le (instr : Arlib.Computation.Op)
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
private theorem natPower_otherSteps_eq (base exponent : ℕ) :
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

/-- INTERNAL: A fixed polynomial absorbs the six opening-charge bounds. -/
private theorem openingPolynomial_arith (S : ℕ) (hS : 1 ≤ S) :
    (S + 7) ^ 2 + (100 * (S + 15) * (2 * S + 30) ^ 2 + 1) +
      1 + (2 * S + 1) + (2 * S + 8) ^ 2 + (2 * S + 12) ^ 2 ≤
      2000000 * S ^ 4 := by
  have h1 : S ≤ S ^ 4 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hS (by decide : 1 ≤ 4))
  have h2 : S ^ 2 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
  have h3 : S ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
  have h4 : 1 ≤ S ^ 4 := by
    simpa only [pow_zero] using (pow_le_pow_right₀ hS (by decide : 0 ≤ 4))
  calc
    _ = 400 * S ^ 3 + 18009 * S ^ 2 + 270096 * S + 1350260 := by ring
    _ ≤ 2000000 * S ^ 4 := by omega

/-- INTERNAL: The thermal setup's rational division fits a quartic size bound. -/
private theorem thermalPolynomial_arith (S : ℕ) (hS : 1 ≤ S) :
    5 + 1120 * S ^ 2 + (S + 1120 * S ^ 2 + 4) ^ 2 ≤
      2000000 * S ^ 4 := by
  have h1 : S ≤ S ^ 2 := by simpa only [pow_one] using
    (pow_le_pow_right₀ hS (by decide : 1 ≤ 2))
  have h2 : S ^ 2 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
  have h4 : 1 ≤ S ^ 4 := by
    simpa only [pow_zero] using (pow_le_pow_right₀ hS (by decide : 0 ≤ 4))
  have hinner : S + 1120 * S ^ 2 + 4 ≤ 1125 * S ^ 2 := by omega
  have hsq := Nat.pow_le_pow_left hinner 2
  calc
    _ ≤ 5 + 1120 * S ^ 2 + (1125 * S ^ 2) ^ 2 := by omega
    _ = 5 + 1120 * S ^ 2 + 1265625 * S ^ 4 := by ring
    _ ≤ 2000000 * S ^ 4 := by omega

/-- INTERNAL: The nonoracle charges of the concrete schedule have a common
polynomial bound in the encoded input size.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_otherSteps_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      otherSteps (CountingMatroid.Program.schedule n p) ≤
        C * inputSize ^ degree := by
  refine ⟨10 ^ 500, 50, ?_⟩
  intro n r p
  have hε := LeastHalvingsCost.leastHalvings_otherSteps_le (p.ε / 10)
  have hδ := LeastHalvingsCost.leastHalvings_otherSteps_le p.δ
  have hbε := leastHalvings_value_le (p.ε / 10)
  have hbδ := leastHalvings_value_le p.δ
  have hεlength : binaryRatLength (p.ε / 10) ≤ binaryRatLength p.ε + 7 := by
    have hten : binaryRatLength (10 : ℚ) = 7 := by decide
    simpa only [hten] using binaryRatLength_div_le p.ε 10
  let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  have hSpos : 0 < S := by dsimp [S]; omega
  have hnS : n ≤ S := by dsimp [S]; omega
  have hεS : binaryRatLength p.ε ≤ S := by
    dsimp [S, binaryInputLength]
    omega
  have hδS : binaryRatLength p.δ ≤ S := by
    dsimp [S, binaryInputLength]
    omega
  have hεlengthS : binaryRatLength (p.ε / 10) ≤ S + 7 := by omega
  have hεden : (p.ε / 10).den.log2 ≤ S + 7 := by
    unfold binaryRatLength binaryNatLength at hεlengthS
    omega
  have hδden : p.δ.den.log2 ≤ S := by
    unfold binaryRatLength binaryNatLength at hδS
    omega
  have hεcost : otherSteps (CountingMatroid.Program.leastHalvings (p.ε / 10)) ≤
      100 * (S + 15) * (2 * S + 30) ^ 2 + 1 := by
    calc
      _ ≤ 100 * ((p.ε / 10).den.log2 + 8) *
          (binaryRatLength (p.ε / 10) + (p.ε / 10).den.log2 + 16) ^ 2 + 1 := hε
      _ ≤ 100 * (S + 15) * (2 * S + 30) ^ 2 + 1 := by
        have h1 : 100 * ((p.ε / 10).den.log2 + 8) ≤ 100 * (S + 15) := by omega
        have h2 : (binaryRatLength (p.ε / 10) +
            (p.ε / 10).den.log2 + 16) ^ 2 ≤ (2 * S + 30) ^ 2 := by
          apply Nat.pow_le_pow_left
          omega
        exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) 1
  have hδcost : otherSteps (CountingMatroid.Program.leastHalvings p.δ) ≤
      100 * (S + 8) * (2 * S + 16) ^ 2 + 1 := by
    calc
      _ ≤ 100 * (p.δ.den.log2 + 8) *
          (binaryRatLength p.δ + p.δ.den.log2 + 16) ^ 2 + 1 := hδ
      _ ≤ 100 * (S + 8) * (2 * S + 16) ^ 2 + 1 := by
        have h1 : 100 * (p.δ.den.log2 + 8) ≤ 100 * (S + 8) := by omega
        have h2 : (binaryRatLength p.δ + p.δ.den.log2 + 16) ^ 2 ≤
            (2 * S + 16) ^ 2 := by
          apply Nat.pow_le_pow_left
          omega
        exact Nat.add_le_add_right (Nat.mul_le_mul h1 h2) 1
  let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
  let L := 2 * n * (n + b)
  let D := 32 * (L + 1)
  let A := 10000000000 * (L + 1) * n ^ 14
  have hbS : b ≤ S + 15 := by dsimp [b]; omega
  have hL : L ≤ 34 * S ^ 2 := by
    have hnb : n + b ≤ 17 * S := by omega
    calc
      L = 2 * n * (n + b) := rfl
      _ ≤ (2 * S) * (17 * S) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hnS) hnb
      _ = 34 * S ^ 2 := by ring
  have hD : D ≤ 1120 * S ^ 2 := by
    have hSsq : 1 ≤ S ^ 2 := by nlinarith
    dsimp [D]
    omega
  have hA : A ≤ 350000000000 * S ^ 16 := by
    have hSsq : 1 ≤ S ^ 2 := by nlinarith
    have hL1 : L + 1 ≤ 35 * S ^ 2 := by omega
    have hn14 : n ^ 14 ≤ S ^ 14 := Nat.pow_le_pow_left hnS 14
    calc
      A = 10000000000 * (L + 1) * n ^ 14 := rfl
      _ ≤ (10000000000 * (35 * S ^ 2)) * S ^ 14 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 10000000000 hL1) hn14
      _ = 350000000000 * S ^ 16 := by
        calc
          10000000000 * (35 * S ^ 2) * S ^ 14 =
              (10000000000 * 35) * (S ^ 2 * S ^ 14) := by ac_rfl
          _ = 350000000000 * S ^ 16 := by norm_num [← pow_add]
  have hDlog : D.log2 ≤ 1120 * S ^ 2 := by
    calc
      D.log2 ≤ D := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 D
      _ ≤ 1120 * S ^ 2 := hD
  have hAlog : A.log2 ≤ 350000000000 * S ^ 16 := by
    calc
      A.log2 ≤ A := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 A
      _ ≤ 350000000000 * S ^ 16 := hA
  have hObsLog :
      ((CountingMatroid.Model.Operations.rationalCeil
        ((A : ℚ) / ((p.ε / (D : ℚ)) * (p.ε / (D : ℚ))))).val).log2 ≤
        A.log2 + 2 * binaryRatLength p.ε + 2 * D.log2 + 12 := by
    exact (rationalCeil_log2_le _).trans
      (observationQuotient_length_le A D p.ε)
  have hObsLogPoly :
      ((CountingMatroid.Model.Operations.rationalCeil
        ((A : ℚ) / ((p.ε / (D : ℚ)) * (p.ε / (D : ℚ))))).val).log2 ≤
        350000000000 * S ^ 16 + 2 * S + 2240 * S ^ 2 + 12 := by
    omega
  rw [schedule_split n p, otherSteps_bind, scheduleOpening_value]
  have hopen := scheduleOpening_otherSteps_le n p
  have hTwoNLog : (2 * n).log2 ≤ 2 * S := by
    calc
      (2 * n).log2 ≤ 2 * n := by
        simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 (2 * n)
      _ ≤ 2 * S := by omega
  have hTwoNLength : binaryRatLength (2 * n : ℚ) ≤ 2 * S + 4 := by
    have h := binaryRatLength_natCast (2 * n)
    simp only [Nat.cast_mul, Nat.cast_ofNat] at h
    omega
  have hInvLength : binaryRatLength (1 / (2 * n : ℚ)) ≤ 2 * S + 8 := by
    have h := binaryRatLength_div_le (1 : ℚ) (2 * n : ℚ)
    have hOne : binaryRatLength (1 : ℚ) = 4 := by decide
    omega
  have hopenPoly : otherSteps (scheduleOpening n p) ≤ 2000000 * S ^ 4 := by
    have h1 : (binaryRatLength p.ε + 7) ^ 2 ≤ (S + 7) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have h2 : (4 + binaryRatLength (2 * n : ℚ)) ^ 2 ≤
        (2 * S + 8) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have h3 : (4 + binaryRatLength (1 / (2 * n : ℚ))) ^ 2 ≤
        (2 * S + 12) ^ 2 := by
      exact Nat.pow_le_pow_left (by omega) 2
    have hbound : otherSteps (scheduleOpening n p) ≤
        (S + 7) ^ 2 + (100 * (S + 15) * (2 * S + 30) ^ 2 + 1) +
        1 + (2 * S + 1) + (2 * S + 8) ^ 2 + (2 * S + 12) ^ 2 := by
      omega
    exact hbound.trans (openingPolynomial_arith S (by omega))
  suffices hremaining :
      otherSteps (scheduleRemaining n p
        ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤ 10 ^ 200 * S ^ 45 by
    change otherSteps (scheduleOpening n p) +
      otherSteps (scheduleRemaining n p
        ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤ 10 ^ 500 * S ^ 50
    have h4 : S ^ 4 ≤ S ^ 50 := pow_le_pow_right₀ (by omega) (by decide)
    have h45 : S ^ 45 ≤ S ^ 50 := pow_le_pow_right₀ (by omega) (by decide)
    have h50 : 1 ≤ S ^ 50 := by
      simpa only [pow_zero] using (pow_le_pow_right₀ (by omega : 1 ≤ S)
        (by decide : 0 ≤ 50))
    have hcost : otherSteps (scheduleOpening n p) +
        otherSteps (scheduleRemaining n p
          ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤
        2000000 * S ^ 4 + 10 ^ 200 * S ^ 45 :=
      Nat.add_le_add hopenPoly hremaining
    omega
  rw [scheduleRemaining_split, otherSteps_bind, thermalSetup_value]
  change otherSteps (thermalSetup n p ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) +
    otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
      10 ^ 200 * S ^ 45
  have hthermal := thermalSetup_otherSteps_le n p
    (⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩ : ScheduleOpeningResult)
  change otherSteps (thermalSetup n p
    ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤
      5 + D.log2 + (binaryRatLength p.ε + binaryRatLength (D : ℚ)) ^ 2 at hthermal
  have hDLength : binaryRatLength (D : ℚ) ≤ 1120 * S ^ 2 + 4 := by
    rw [binaryRatLength_natCast]
    omega
  have hinner : binaryRatLength p.ε + binaryRatLength (D : ℚ) ≤
      S + 1120 * S ^ 2 + 4 := by omega
  have hthermalPoly : otherSteps (thermalSetup n p
      ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤ 2000000 * S ^ 4 := by
    have hsq := Nat.pow_le_pow_left hinner 2
    have hbound : otherSteps (thermalSetup n p
        ⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩) ≤
        5 + 1120 * S ^ 2 + (S + 1120 * S ^ 2 + 4) ^ 2 := by omega
    exact hbound.trans (thermalPolynomial_arith S (by omega))
  suffices htail : otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
        10 ^ 150 * S ^ 40 by
    have h4 : S ^ 4 ≤ S ^ 45 := pow_le_pow_right₀ (by omega) (by decide)
    have h40 : S ^ 40 ≤ S ^ 45 := pow_le_pow_right₀ (by omega) (by decide)
    have h45 : 1 ≤ S ^ 45 := by
      simpa only [pow_zero] using (pow_le_pow_right₀ (by omega : 1 ≤ S)
        (by decide : 0 ≤ 45))
    have hcost := Nat.add_le_add hthermalPoly htail
    omega
  exact thermalRest_otherSteps_poly n r p

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r14b · pending · the parent elaborates through the isolated tail lemma;
  the live handoff request was refused before capture.
* r14 · recovery · split the schedule into opening, thermal setup, and tail;
  proved the first two cost bounds and handed off the isolated tail bound.
* r13 · partial · proved the observation-quotient length and its ceiling-log
  polynomial bound and input-size bounds for both halving searches;
  schedule-cost normalization remains open.
* r12 · partial · proved capped-loop, rational-length, and ceiling-logarithm
  helpers; the full schedule sum still needs intermediate-value bookkeeping.
* r11 · partial · proved charged sequencing and natural-power costs; isolated the
  halving-loop cost and imported its checked child statement. The full schedule
  cost still needs rational operand-size bounds and a sum of all primitive costs.
-/
