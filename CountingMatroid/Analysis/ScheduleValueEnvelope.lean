import CountingMatroid.Model.Run
import CountingMatroid.Analysis.BoundedRunResourceEnvelope

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleValueEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: A bounded charged search whose first state component rises by at
most one per successful round cannot exceed its round cap. -/
private theorem firstCounter_foldlWhile_le {α β : Type}
    (f : (ℕ × β) → α → Arlib.Computation.Charged Op Cell (Option (ℕ × β)))
    (hstep : ∀ b a b', (f b a).val = some b' → b'.1 ≤ b.1 + 1)
    (l : List α) (b : ℕ × β) :
    (Arlib.Computation.Charged.foldlWhile f l b).val.1 ≤ b.1 + l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    cases h : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at h
      simp [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val, h]
    | some b' =>
      have hs := hstep b a b' h
      have hr := ih b'
      simp only [Arlib.Computation.Charged.val] at h
      simp only [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val,
        h, List.length_cons] at *
      omega

/-- INTERNAL: The halving search is bounded by its encoded denominator cap.
TEXLINE: main.tex:1348-1351 -/
private theorem leastHalvings_val_le_den (q : ℚ) :
    (CountingMatroid.Program.leastHalvings q).val ≤ q.den.log2 + 8 := by
  unfold CountingMatroid.Program.leastHalvings
  simp only [Arlib.Computation.Charged.val_bind,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure]
  unfold Arlib.Computation.Charged.repeatWhile
  convert firstCounter_foldlWhile_le (f := _) ?_ (List.range (q.den.log2 + 8))
    (0, (1 : ℚ)) using 1 <;> simp
  intro b a b' b'q h
  split at h
  · simp only [successor, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_map,
      Arlib.Computation.Charged.val_op, ratDiv,
      Arlib.Computation.Charged.val_opMany] at h
    cases h
    omega
  · simp at h

/-- INTERNAL: Dividing a rational by ten increases its denominator's binary
length by at most four.
TEXLINE: main.tex:1348-1351 -/
private theorem rat_div_ten_den_log2_le (q : ℚ) :
    (q / 10).den.log2 ≤ q.den.log2 + 4 := by
  have hdvd : (q / 10).den ∣ q.den * 10 := by
    convert Rat.mul_den_dvd q (1 / 10 : ℚ) using 1 <;> norm_num [div_eq_mul_inv]
  have hden : (q / 10).den ≤ q.den * 10 :=
    Nat.le_of_dvd (by positivity) hdvd
  have h16 : q.den * 10 ≤ q.den * 16 := by omega
  rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
  calc
    Nat.log 2 (q / 10).den ≤ Nat.log 2 (q.den * 16) :=
      Nat.log_mono_right (le_trans hden h16)
    _ = Nat.log 2 q.den + 4 := by
      have hq : q.den ≠ 0 := q.den_nz
      have hqpos : 0 < q.den := q.den_pos
      conv_lhs => rw [show (16 : ℕ) = 2 * 2 * 2 * 2 by decide]
      simp only [← mul_assoc]
      rw [Nat.log_mul_base (by decide : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by decide : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by decide : 1 < 2) (by positivity)]
      rw [Nat.log_mul_base (by decide : 1 < 2) hq]

/-- INTERNAL: The drawing-width search is bounded by its binary cap.
TEXLINE: main.tex:1397-1421 -/
private theorem leastDrawTrials_val_le_cap (M : ℕ) :
    (CountingMatroid.Program.leastDrawTrials M).val ≤ M.log2 + 9 := by
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [Arlib.Computation.Charged.val_bind,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure]
  unfold Arlib.Computation.Charged.repeatWhile
  convert firstCounter_foldlWhile_le (f := _) ?_ (List.range (M.log2 + 8))
    (1, 2) using 1 <;> simp
  case e'_4 => omega
  intro b a b' b'q h
  split at h
  · simp only [successor, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_map, Arlib.Computation.Charged.val_op,
      natMul] at h
    cases h
    omega
  · simp at h

/-- INTERNAL: The repetition count is ten times the confidence halving count,
plus one.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_repetitions_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.repetitions =
      10 * (CountingMatroid.Program.leastHalvings p.δ).val + 1 := by
  unfold CountingMatroid.Program.schedule
  simp only [Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, natMul, successor,
    Arlib.Computation.Charged.val_op]

/-- INTERNAL: The schedule's repetition count is linear in the input encoding.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_repetitions_le_input (n r : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.repetitions ≤
      10 * binaryInputLength n r p + 81 := by
  rw [schedule_repetitions_eq]
  have h := leastHalvings_val_le_den p.δ
  unfold binaryInputLength binaryRatLength binaryNatLength
  omega

/-- INTERNAL: The phase cap records the first halving search in the concrete
schedule formula.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_L_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.L =
      2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) := by
  unfold CountingMatroid.Program.schedule
  simp only [Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, natMul, natAdd, ratDiv,
    Arlib.Computation.Charged.val_op,
    Arlib.Computation.Charged.val_opMany]

/-- INTERNAL: The phase count is quadratic in the ground size and input
encoding length.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_L_le_input (n r : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.L ≤
      2 * n * (n + binaryInputLength n r p + 12) := by
  rw [schedule_L_eq]
  have hcap := leastHalvings_val_le_den (p.ε / 10)
  have hlog := rat_div_ten_den_log2_le p.ε
  have hbound :
      (CountingMatroid.Program.leastHalvings (p.ε / 10)).val ≤
        binaryInputLength n r p + 12 := by
    unfold binaryInputLength binaryRatLength binaryNatLength
    omega
  exact Nat.mul_le_mul_left _ (Nat.add_le_add_left hbound n)

/-- INTERNAL: The trace length is the paper's explicit polynomial in the phase cap.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_tau_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.τ =
      20 * n ^ 4 *
        (n * (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) + 2) := by
  rfl

/-- INTERNAL: The restart cap is determined by the phase cap and trace length.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_restartCap_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.restartCap =
      2000 * ((CountingMatroid.Program.schedule n p).val.L + 1) ^ 2 * n ^ 2 *
        (CountingMatroid.Program.schedule n p).val.τ := by
  rfl

/-- INTERNAL: The observation count is the ceiling of the charged rational
quotient. TEXLINE: main.tex:1348-1355 -/
private theorem schedule_observations_eq (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.observations =
      Nat.ceil (((10000000000 *
          (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) *
          n ^ 14 : ℕ) : ℚ) /
        (p.ε / (↑(32 *
          (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)) : ℚ)) ^ 2) := by
  have hraw :
      (CountingMatroid.Program.schedule n p).val.observations =
        Int.toNat (((((10000000000 *
            (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) *
            (CountingMatroid.Program.natPower n 14).val : ℕ) : ℚ) /
          ((p.ε / (↑(32 *
            (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)) : ℚ)) *
           (p.ε / (↑(32 *
            (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)) : ℚ))))).ceil) := by
    rfl
  have hceil (q : ℚ) : q.ceil = ⌈q⌉ := by
    symm
    apply Int.ceil_eq_iff.mpr
    constructor
    · have h := Rat.ceil_lt (x := q)
      linarith
    · exact Rat.le_ceil
  rw [hceil, Int.ceil_toNat,
    CountingMatroid.Analysis.BoundedRunResourceEnvelope.natPower_value,
    ← pow_two] at hraw
  exact hraw

/-- INTERNAL: The observation count is bounded using the ceiling of inverse
accuracy, so the rational division cannot make it superpolynomial.
TEXLINE: main.tex:1348-1355 -/
private theorem schedule_observations_le (n : ℕ) (p : InputParams) :
    (CountingMatroid.Program.schedule n p).val.observations ≤
      10000000000 * ((CountingMatroid.Program.schedule n p).val.L + 1) * n ^ 14 *
        (32 * ((CountingMatroid.Program.schedule n p).val.L + 1)) ^ 2 *
        (Nat.ceil p.ε⁻¹) ^ 2 := by
  rw [schedule_observations_eq, schedule_L_eq]
  let A := 10000000000 *
    (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1) * n ^ 14
  let B := 32 *
    (2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) + 1)
  change Nat.ceil ((A : ℚ) / (p.ε / (B : ℚ)) ^ 2) ≤
    A * B ^ 2 * (Nat.ceil p.ε⁻¹) ^ 2
  rw [Nat.ceil_le]
  have h : (A : ℚ) / (p.ε / (B : ℚ)) ^ 2 =
      (A : ℚ) * (B : ℚ) ^ 2 * p.ε⁻¹ ^ 2 := by
    field_simp
  rw [h]
  push_cast
  gcongr
  · exact (inv_pos.mpr p.ε_pos).le
  · exact Nat.le_ceil _



/-- INTERNAL: The concrete schedule fields have a common polynomial envelope
in the encoded input size.
TEXLINE: main.tex:1348-1356, 1397-1421 -/
theorem schedule_value_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let s := (CountingMatroid.Program.schedule n p).val
      n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
        binaryRatLength s.ρ + s.repetitions + 1 ≤ C * inputSize ^ degree := by
  -- BLOCKER: schedule_observations_le now bounds the eta⁻² ceiling. The
  -- remaining goal is to combine all explicit field bounds into one power
  -- of inputSize. This still needs a bound on binaryRatLength s.ρ, which
  -- requires numerator and denominator bounds for 1 - 1 / (2 * n).
  sorry

end CountingMatroid.Analysis.ScheduleValueEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r9 · partial · proved tau and restart formulas and a polynomial observation ceiling bound; the rho encoding and common envelope remain open.
* r8 · open · proved search caps, denominator growth under division by ten, and L and repetition bounds; full value envelope still needs observation quotient and later-field bounds.
-/
