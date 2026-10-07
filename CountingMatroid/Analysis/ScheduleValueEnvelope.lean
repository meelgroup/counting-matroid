import CountingMatroid.Model.Run
import CountingMatroid.Analysis.BoundedRunResourceEnvelope
import CountingMatroid.Analysis.ScheduleDrawTrialsBridge

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

/-- INTERNAL: A rational in the unit interval has an encoding controlled by
its denominator. TEXLINE: main.tex:1348-1356 -/
private theorem binaryRatLength_le_den_of_unit (q : ℚ)
    (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : binaryRatLength q ≤ 2 * q.den + 4 := by
  have hn0 : 0 ≤ q.num := Rat.num_nonneg.mpr hq0
  have hn1 : q.num ≤ (q.den : ℤ) := by
    have h := hq1
    rw [← q.num_div_den] at h
    have h' : (q.num : ℚ) ≤ (q.den : ℚ) := by
      simpa using (div_le_iff₀ (by exact_mod_cast q.den_pos)).mp h
    exact_mod_cast h'
  have hn : q.num.natAbs ≤ q.den := by
    have hn' : (q.num.natAbs : ℤ) ≤ (q.den : ℤ) := by
      simpa [Int.natAbs_of_nonneg hn0] using hn1
    exact_mod_cast hn'
  unfold binaryRatLength binaryNatLength
  have hlogn := Nat.log_le_self 2 q.num.natAbs
  have hlogd := Nat.log_le_self 2 q.den
  simp only [Nat.log2_eq_log_two]
  omega

/-- INTERNAL: The annealing ratio has denominator at most twice the ground size.
TEXLINE: main.tex:1348-1356 -/
private theorem schedule_rho_length_le (n : ℕ) (p : InputParams) :
    binaryRatLength (CountingMatroid.Program.schedule n p).val.ρ ≤ 4 * n + 6 := by
  have hρ : (CountingMatroid.Program.schedule n p).val.ρ =
      1 - 1 / (2 * n : ℚ) := by
    unfold CountingMatroid.Program.schedule
    simp only [Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, natMul, ratOfNat, ratDiv, ratSub,
      Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany]
    norm_num [Nat.cast_mul]
  rw [hρ]
  by_cases hn : n = 0
  · subst n
    simp [binaryRatLength, binaryNatLength, Nat.log2_eq_log_two]
  · have hnp : 0 < n := Nat.pos_of_ne_zero hn
    have hden : (1 - 1 / (2 * n : ℚ)).den = 2 * n := by
      have hcast : (2 * n : ℚ) = ((2 * n : ℕ) : ℚ) := by norm_num [Nat.cast_mul]
      rw [hcast, one_div, show (1 : ℚ) = ((1 : ℕ) : ℚ) by norm_num,
        Rat.natCast_sub_den, Rat.inv_natCast_den_of_pos (by omega : 0 < 2 * n)]
    have hunit0 : 0 ≤ (1 - 1 / (2 * n : ℚ)) := by
      have : (1 : ℚ) ≤ 2 * n := by exact_mod_cast (by omega : 1 ≤ 2 * n)
      have : 1 / (2 * n : ℚ) ≤ 1 := (div_le_iff₀ (by positivity)).2 (by nlinarith)
      linarith
    have hunit1 : (1 - 1 / (2 * n : ℚ)) ≤ 1 := by
      have : 0 ≤ 1 / (2 * n : ℚ) := by positivity
      linarith
    have hb := binaryRatLength_le_den_of_unit _ hunit0 hunit1
    rw [hden] at hb
    omega




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
  refine ⟨10 ^ 500, 50, ?_⟩
  intro n r p
  let s := (CountingMatroid.Program.schedule n p).val
  let X := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  have hdraw := ScheduleDrawTrialsBridge.schedule_drawTrials_le_drawCalls n p
  have hrho := schedule_rho_length_le n p
  change s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9 at hdraw
  change binaryRatLength s.ρ ≤ 4 * n + 6 at hrho
  let Y := 10000000000 * X
  have hX : 1 ≤ X := by dsimp [X]; omega
  have hnX : n ≤ X := by dsimp [X]; omega
  have hbinX : binaryInputLength n r p ≤ X := by dsimp [X]; omega
  have hεX : Nat.ceil p.ε⁻¹ ≤ X := by dsimp [X]; omega
  have hY : 10000000000 ≤ Y := by dsimp [Y]; nlinarith
  have hnY : n ≤ Y := by dsimp [Y]; omega
  have hεY : Nat.ceil p.ε⁻¹ ≤ Y := by dsimp [Y]; omega
  have hLY : s.L ≤ Y ^ 2 := by
    have hL := schedule_L_le_input n r p
    change s.L ≤ 2 * n * (n + binaryInputLength n r p + 12) at hL
    calc
      s.L ≤ 2 * n * (n + binaryInputLength n r p + 12) := hL
      _ ≤ 2 * X * (14 * X) := by gcongr <;> omega
      _ = 28 * X ^ 2 := by ring
      _ ≤ Y ^ 2 := by
        calc
          28 * X ^ 2 ≤ 10000000000 ^ 2 * X ^ 2 := by gcongr; norm_num
          _ = Y ^ 2 := by dsimp [Y]; ring
  have hY1 : 1 ≤ Y := by omega
  have hY2 : 2 ≤ Y := by omega
  have hLp : s.L + 1 ≤ Y ^ 3 := by
    have hpow : 1 ≤ Y ^ 2 := one_le_pow₀ hY1
    calc
      s.L + 1 ≤ Y ^ 2 + 1 := by omega
      _ ≤ 2 * Y ^ 2 := by omega
      _ ≤ Y * Y ^ 2 := Nat.mul_le_mul_right _ hY2
      _ = Y ^ 3 := by ring
  have hinner : n * (s.L + 1) + 2 ≤ Y ^ 5 := by
    have hY4 : 2 ≤ Y ^ 4 := by
      exact hY2.trans (le_self_pow hY1 (by decide))
    calc
      n * (s.L + 1) + 2 ≤ Y * Y ^ 3 + 2 := by gcongr
      _ = Y ^ 4 + 2 := by ring
      _ ≤ 2 * Y ^ 4 := by omega
      _ ≤ Y * Y ^ 4 := Nat.mul_le_mul_right _ hY2
      _ = Y ^ 5 := by ring
  change n + s.L + s.τ + s.restartCap + s.observations + s.drawTrials +
    binaryRatLength s.ρ + s.repetitions + 1 ≤ 10 ^ 500 * X ^ 50
  calc
    _ ≤ n + s.L + s.τ + s.restartCap + s.observations +
        ((3 * s.L * (s.restartCap + s.observations)).log2 + 9) +
        (4 * n + 6) + s.repetitions + 1 := by omega
    _ ≤ 10 ^ 500 * X ^ 50 := by
      -- BLOCKER: L and its inner trace factor are bounded above. Rewriting
      -- the expanded tau formula to use those bounds exceeded the heartbeat
      -- limit both through an s.τ equality and through schedule_tau_eq.
      -- Restart, observation, and final monomial estimates remain.
      sorry

end CountingMatroid.Analysis.ScheduleValueEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r10 · partial · proved rho and L bounds, including n=0; separated the draw-trial bridge and encountered heartbeat limits combining the explicit tau formula.
* r9 · partial · proved tau and restart formulas and a polynomial observation ceiling bound; the rho encoding and common envelope remain open.
* r8 · open · proved search caps, denominator growth under division by ten, and L and repetition bounds; full value envelope still needs observation quotient and later-field bounds.
-/
