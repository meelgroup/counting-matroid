import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

open CountingMatroid.Model.Operations
open Arlib.Computation

/-- INTERNAL: One charged iteration of the denominator halving search. -/
private def halfStep (δ : ℚ) (_ : ℕ) (acc : ℕ × ℚ) :
    Charged CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
      (Option (ℕ × ℚ)) := do
  let needsStep ← ratLess δ acc.2
  if needsStep then
    let b ← successor acc.1
    let power ← ratDiv acc.2 2
    pure (some (b, power))
  else pure none

/-- INTERNAL: The charged halving step has the expected numerical value. -/
private theorem halfStep_val (δ : ℚ) (i : ℕ) (acc : ℕ × ℚ) :
    (halfStep δ i acc).val =
      if δ < acc.2 then some (acc.1 + 1, acc.2 / 2) else none := by
  by_cases h : δ < acc.2 <;> simp [halfStep, ratLess, h, successor, ratDiv]

/-- INTERNAL: Value equation for a charged loop with early exit. -/
private theorem val_cons {β : Type}
    (f : ℕ → β → Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell (Option β))
    (i : ℕ) (l : List ℕ) (b : β) :
    (Charged.foldlWhile (fun b i => f i b) (i :: l) b).val =
      match (f i b).val with
      | none => b
      | some b' => (Charged.foldlWhile (fun b i => f i b) l b').val := by
  cases h : (f i b).val with
  | none =>
    simp only [Charged.val] at h
    simp [Charged.foldlWhile, Charged.val, h]
  | some b' =>
    simp only [Charged.val] at h
    simp [Charged.foldlWhile, Charged.val, h]

/-- INTERNAL: A halving loop that runs long enough or exits early satisfies the threshold. -/
private theorem loop_bound (δ : ℚ) :
    ∀ (l : List ℕ) (b : ℕ) (power : ℚ),
      power = (1 / 2 : ℚ) ^ b →
      (1 / 2 : ℚ) ^ (b + l.length) ≤ δ →
      (1 / 2 : ℚ) ^
        ((Charged.foldlWhile (fun acc i => halfStep δ i acc) l (b, power)).val.1) ≤ δ := by
  intro l
  induction l with
  | nil =>
    intro b power hp hbound
    change (1 / 2 : ℚ) ^ b ≤ δ
    simpa using hbound
  | cons i l ih =>
    intro b power hp hbound
    rw [val_cons, halfStep_val]
    by_cases h : δ < power
    · simp only [if_pos h]
      apply ih
      · rw [hp, pow_succ]; ring
      · calc
          (1 / 2 : ℚ) ^ (b + 1 + l.length) =
            (1 / 2 : ℚ) ^ (b + (i :: l).length) := by congr 1; simp; omega
          _ ≤ δ := hbound
    · simp only [if_neg h]
      simpa [hp] using (le_of_not_gt h)

/-- INTERNAL: The binary length cap is sufficient for every positive rational threshold. -/
private theorem cap_bound (δ : ℚ) (hδ : 0 < δ) :
    (1 / 2 : ℚ) ^ (δ.den.log2 + 8) ≤ δ := by
  have hnat : δ.den ≤ 2 ^ (δ.den.log2 + 8) := by
    have ht := Nat.lt_pow_succ_log_self Nat.one_lt_two δ.den
    rw [← Nat.log2_eq_log_two] at ht
    calc
      δ.den ≤ 2 ^ (δ.den.log2 + 1) := Nat.le_of_lt ht
      _ ≤ 2 ^ (δ.den.log2 + 8) := by gcongr <;> omega
  have hden : (0 : ℚ) < δ.den := by exact_mod_cast δ.den_pos
  have hpow : (0 : ℚ) < (2 : ℚ) ^ (δ.den.log2 + 8) := by positivity
  have hnum : (1 : ℚ) ≤ (δ.num : ℚ) := by
    have := Rat.num_pos.mpr hδ
    exact_mod_cast this
  conv_rhs => rw [← δ.num_div_den]
  rw [one_div, inv_pow]
  rw [inv_eq_one_div]
  apply (div_le_div_iff₀ hpow hden).mpr
  nlinarith [show (δ.den : ℚ) ≤ (2 : ℚ) ^ (δ.den.log2 + 8) by exact_mod_cast hnat]

/-- INTERNAL: The charged least-halvings search meets its rational threshold. -/
private theorem least_bound (δ : ℚ) (hδ : 0 < δ) :
    (1 / 2 : ℚ) ^ (CountingMatroid.Program.leastHalvings δ).val ≤ δ := by
  unfold CountingMatroid.Program.leastHalvings
  simp only [Charged.val_bind, CountingMatroid.Model.Operations.binaryLoopBound,
    Charged.val_op, Charged.val_pure, Charged.repeatWhile]
  apply loop_bound δ (List.range (δ.den.log2 + 8)) 0 1
  · simp
  · simpa using cap_bound δ hδ

/-- INTERNAL: Transfer a positive rational threshold bound to `ENNReal`. -/
private theorem enn_bound (δ : ℚ) (b : ℕ)
    (hb : (1 / 2 : ℚ) ^ b ≤ δ) :
    (1 / 2 : ENNReal) ^ b ≤ ENNReal.ofReal (δ : ℝ) := by
  have hreal : (1 / 2 : ℝ) ^ b ≤ (δ : ℝ) := by
    have hc : (((1 / 2 : ℚ) ^ b : ℚ) : ℝ) ≤ (δ : ℝ) := by exact_mod_cast hb
    simpa only [Rat.cast_pow, Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] using hc
  have h := ENNReal.ofReal_le_ofReal hreal
  rw [ENNReal.ofReal_pow (by positivity)] at h
  have heq : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  simpa only [heq] using h

/-- INTERNAL: The public schedule exposes the charged halving count. -/
private theorem setup_bδ (n : ℕ) (p : CountingMatroid.Model.InputParams) :
    (CountingMatroid.Interface.Pseudocode.setup n p).bδ =
      (CountingMatroid.Program.leastHalvings p.δ).val := by
  dsimp [CountingMatroid.Interface.Pseudocode.setup, CountingMatroid.Program.schedule]

/-- INTERNAL: The charged schedule implements the paper's repetition count and
halving threshold, in the numerical form needed by amplification.
TEXLINE: main.tex:1442-1446 -/
theorem schedule_confidence_bound (n : ℕ) (p : CountingMatroid.Model.InputParams) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    s.repetitions = 10 * s.bδ + 1 ∧
      (1 / 2 : ENNReal) ^ s.bδ ≤ ENNReal.ofReal (p.δ : ℝ) := by
  constructor
  · dsimp [CountingMatroid.Interface.Pseudocode.setup, CountingMatroid.Program.schedule]
    simp [CountingMatroid.Model.Operations.successor,
      CountingMatroid.Model.Operations.natMul, Arlib.Computation.Charged.val_op]
  · rw [setup_bδ]
    exact enn_bound p.δ _ (least_bound p.δ p.δ_pos)

end CountingMatroid.Analysis.MedianAmplification

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · established the charged halving loop invariant and denominator cap bound.
-/
