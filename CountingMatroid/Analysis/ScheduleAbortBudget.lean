import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false

/-!
The concrete doubling search meets the capped-draw probability threshold.
The schedule budget combines its per-phase draw terms with the restart-tail
term. These are deterministic numerical bounds; operational event bounds
are supplied separately by the conditional abort modules.
-/

namespace CountingMatroid.Analysis.ScheduleAbortBudget

open CountingMatroid.Model CountingMatroid.Model.Operations
open Arlib.Computation (Charged)

/-- INTERNAL: One charged iteration of the actual draw-trial doubling search. -/
private def doublingStep (target : ℕ) (acc : ℕ × ℕ) (_ : ℕ) :
    Charged Op Cell (Option (ℕ × ℕ)) := do
  let needsStep ← lessThan acc.2 target
  if needsStep then
    let d ← successor acc.1
    let power ← natMul acc.2 2
    pure (some (d, power))
  else pure none

/-- INTERNAL: Value equation for the capped doubling search. -/
private theorem doubling_cons
    (target : ℕ) (i : ℕ) (l : List ℕ) (acc : ℕ × ℕ) :
    (Charged.foldlWhile (doublingStep target) (i :: l) acc).val =
      if acc.2 < target then
        (Charged.foldlWhile (doublingStep target) l (acc.1 + 1, acc.2 * 2)).val
      else acc := by
  by_cases h : acc.2 < target
  · have hs : (doublingStep target acc i).val = some (acc.1 + 1, acc.2 * 2) := by
      simp [doublingStep, lessThan, successor, natMul, h]
    simp only [Charged.val] at hs
    simp [Charged.foldlWhile, Charged.val, hs, h]
  · have hs : (doublingStep target acc i).val = none := by
      simp [doublingStep, lessThan, h]
    simp only [Charged.val] at hs
    simp [Charged.foldlWhile, Charged.val, hs, h]

/-- INTERNAL: The doubling search reaches its threshold or stops only after
it has already met it. -/
private theorem doubling_threshold (target : ℕ) :
    ∀ (l : List ℕ) (d power : ℕ), power = 2 ^ d →
      target ≤ 2 ^ (d + l.length) →
      target ≤ 2 ^ (Charged.foldlWhile (doublingStep target) l (d, power)).val.1 := by
  intro l
  induction l with
  | nil =>
      intro d power hp ht
      simpa using ht
  | cons i l ih =>
      intro d power hp ht
      rw [doubling_cons]
      by_cases h : power < target
      · rw [if_pos h]
        apply ih
        · rw [hp, pow_succ]
        · simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm 1] using ht
      · rw [if_neg h]
        simpa only [hp] using le_of_not_gt h

/-- INTERNAL: The actual capped integer search meets the paper's rejection
probability threshold, including zero requested calls.
TEXLINE: main.tex:1405-1421 -/
theorem least_draw_trials_threshold (M : ℕ) :
    32 * M ≤ 2 ^ (CountingMatroid.Program.leastDrawTrials M).val := by
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [Charged.val_bind, binaryLoopBound, Charged.val_op,
    Charged.val_pure, natMul, Charged.repeatWhile]
  change 32 * M ≤ 2 ^ (Charged.foldlWhile (doublingStep (32 * M))
    (List.range (M.log2 + 8)) (1, 2)).val.1
  apply doubling_threshold (32 * M) (List.range (M.log2 + 8)) 1 2 (by norm_num)
  have hM : M ≤ 2 ^ (M.log2 + 1) := by
    have h := Nat.lt_pow_succ_log_self Nat.one_lt_two M
    rw [← Nat.log2_eq_log_two] at h
    exact Nat.le_of_lt h
  simp only [List.length_range]
  calc
    32 * M ≤ 32 * 2 ^ (M.log2 + 1) := Nat.mul_le_mul_left _ hM
    _ = 2 ^ (M.log2 + 6) := by
      simp only [pow_add]
      norm_num
      omega
    _ ≤ 2 ^ (1 + (M.log2 + 8)) := pow_le_pow_right' (by decide : 1 ≤ (2 : ℕ)) (by omega)

/-- INTERNAL: Numerical form of the per-phase restart and draw budget,
separated from schedule evaluation so arithmetic does not unfold the program.
TEXLINE: main.tex:1233-1239,1405-1421 -/
private theorem abort_budget_of_threshold (L B N D : ℕ)
    (hLnat : 0 < L) (ht : 32 * (3 * L * (B + N)) ≤ 2 ^ D) :
    (L : ℚ) / (100 * ((L : ℚ) + 1) ^ 2) +
      3 * (B : ℚ) * (1 / 2 : ℚ) ^ D +
      3 * (N : ℚ) * (1 / 2 : ℚ) ^ D ≤ 3 / (32 * ((L : ℚ) + 1)) := by
  have hL : (1 : ℚ) ≤ L := by exact_mod_cast hLnat
  have htq : 32 * (3 * (L : ℚ) * ((B : ℚ) + N)) ≤ (2 : ℚ) ^ D := by
    exact_mod_cast ht
  have hdraw : 3 * ((B : ℚ) + N) * (1 / 2 : ℚ) ^ D ≤
      1 / (16 * ((L : ℚ) + 1)) := by
    rw [div_pow, one_pow, mul_one_div]
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    have hc : 16 * ((L : ℚ) + 1) ≤ 32 * L := by linarith
    calc
      _ ≤ (3 * ((B : ℚ) + N)) * (32 * L) := by
        exact mul_le_mul_of_nonneg_left hc (by positivity)
      _ ≤ _ := by nlinarith [htq]
  have htail : (L : ℚ) / (100 * ((L : ℚ) + 1) ^ 2) ≤
      1 / (32 * ((L : ℚ) + 1)) := by
    apply (div_le_div_iff₀ (by positivity) (by positivity)).mpr
    nlinarith [sq_nonneg (L : ℚ)]
  calc
    _ = (L : ℚ) / (100 * ((L : ℚ) + 1) ^ 2) +
        3 * ((B : ℚ) + N) * (1 / 2 : ℚ) ^ D := by ring
    _ ≤ 1 / (32 * ((L : ℚ) + 1)) +
        1 / (16 * ((L : ℚ) + 1)) := add_le_add htail hdraw
    _ = _ := by field_simp; ring

/-- INTERNAL: The fields relevant to the rejection probability threshold. -/
private def drawFieldsGood (s : AnnealingSchedule) : Prop :=
  32 * (3 * s.L * (s.restartCap + s.observations)) ≤ 2 ^ s.drawTrials

/-- INTERNAL: Transfer a property of charged continuation values through a bind. -/
private theorem val_bind_property {α β : Type}
    (c : Charged Op Cell α) (f : α → Charged Op Cell β)
    (P : β → Prop) (h : ∀ x, P (f x).val) : P (c >>= f).val := by
  simpa only [Charged.val_bind] using h c.val

/-- INTERNAL: The final schedule operations store a sufficient draw-trial count. -/
private theorem schedule_tail_good (bε : ℕ) (rho : ℚ) (L : ℕ) (eta : ℚ)
    (tau restartCap observations : ℕ) (p : InputParams) :
    drawFieldsGood (do
      let attemptsAndObservations ← natAdd restartCap observations
      let threeL ← natMul 3 L
      let drawCalls ← natMul threeL attemptsAndObservations
      let drawTrials ← CountingMatroid.Program.leastDrawTrials drawCalls
      let bδ ← CountingMatroid.Program.leastHalvings p.δ
      let tenBδ ← natMul 10 bδ
      let repetitions ← successor tenBδ
      pure (AnnealingSchedule.mk bε rho L eta tau restartCap observations
        drawCalls drawTrials bδ repetitions) : Charged Op Cell AnnealingSchedule).val := by
  simp only [Charged.val_bind, Charged.val_pure, natAdd, natMul,
    Charged.val_op, drawFieldsGood]
  exact least_draw_trials_threshold _

/-- INTERNAL: The charged schedule satisfies its capped-draw threshold.
TEXLINE: main.tex:1405-1421 -/
theorem schedule_draw_threshold (n : ℕ) (p : InputParams) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    32 * (3 * s.L * (s.restartCap + s.observations)) ≤ 2 ^ s.drawTrials := by
  change drawFieldsGood (CountingMatroid.Program.schedule n p).val
  unfold CountingMatroid.Program.schedule
  iterate 29
    apply val_bind_property
    intro
  exact schedule_tail_good _ _ _ _ _ _ _ p

/-- INTERNAL: A positive ground size gives a positive phase count.
TEXLINE: main.tex:1116-1126 -/
private theorem schedule_phase_count_pos (n : ℕ) (p : InputParams) (hn : 0 < n) :
    0 < (CountingMatroid.Interface.Pseudocode.setup n p).L := by
  have hLformula : (CountingMatroid.Interface.Pseudocode.setup n p).L =
      2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) := by
    simp only [CountingMatroid.Interface.Pseudocode.setup,
      CountingMatroid.Program.schedule, Charged.val_bind, Charged.val_pure,
      natMul, natAdd, ratDiv, Charged.val_op, Charged.val_opMany]
  rw [hLformula]
  positivity

/-- INTERNAL: The schedule's restart-tail term and per-phase capped-draw
terms fit the conditional execution-abort budget. The extra factor two in
the draw budget covers `L + 1 ≤ 2L` for positive ground size.
TEXLINE: main.tex:1233-1239,1405-1421 -/
theorem schedule_abort_budget (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    (s.L : ℚ) / (100 * ((s.L : ℚ) + 1) ^ 2) +
      3 * (s.restartCap : ℚ) * (1 / 2 : ℚ) ^ s.drawTrials +
      3 * (s.observations : ℚ) * (1 / 2 : ℚ) ^ s.drawTrials ≤
        3 / (32 * ((s.L : ℚ) + 1)) := by
  exact abort_budget_of_threshold _ _ _ _ (schedule_phase_count_pos n p hn)
    (schedule_draw_threshold n p)

end CountingMatroid.Analysis.ScheduleAbortBudget

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r24 · proved · the actual capped doubling search meets `32*M ≤ 2^D`; positive phase count and the charged schedule tail give the combined `3/[32(L+1)]` abort budget. Direct field reduction was replaced by continuation-property propagation and separate numerical arithmetic.
-/
