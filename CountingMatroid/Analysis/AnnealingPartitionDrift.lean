import CountingMatroid.Analysis.FirstPhaseFailure
import Mathlib.Algebra.Order.Ring.Pow

set_option autoImplicit false

namespace CountingMatroid.Analysis.AnnealingPartitionDrift

open CountingMatroid.Model

/-- PAPER: main.tex:1131-1145
The schedule's cooling factor is positive, at most one, and its nth power
is at least one half. This uses Bernoulli's inequality, not a rank promise. -/
theorem schedule_power_lower (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let ρ := (CountingMatroid.Interface.Pseudocode.setup n p).ρ
    0 < ρ ∧ ρ ≤ 1 ∧ (1 / 2 : ℚ) ≤ ρ ^ n := by
  have hρ : (CountingMatroid.Interface.Pseudocode.setup n p).ρ =
      1 - 1 / (2 * (n : ℚ)) := by
    simp only [CountingMatroid.Interface.Pseudocode.setup,
      CountingMatroid.Program.schedule, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure,
      CountingMatroid.Model.Operations.ratDiv,
      CountingMatroid.Model.Operations.ratSub,
      CountingMatroid.Model.Operations.ratOfNat,
      CountingMatroid.Model.Operations.natMul,
      Arlib.Computation.Charged.val_op,
      Arlib.Computation.Charged.val_opMany]
    norm_cast
  dsimp only
  rw [hρ]
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hn1 : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hden : (0 : ℚ) < 2 * n := by positivity
  have hinv : (1 : ℚ) / (2 * n) ≤ 1 / 2 := by
    apply (div_le_iff₀ hden).mpr
    linarith
  have hpos : (0 : ℚ) < 1 - 1 / (2 * n) := by linarith
  have hle : (1 - 1 / (2 * (n : ℚ))) ≤ 1 :=
    sub_le_self _ (by positivity)
  refine ⟨hpos, hle, ?_⟩
  have hbern := one_add_mul_sub_le_pow
    (show (-1 : ℚ) ≤ 1 - 1 / (2 * n) by linarith) n
  have heq : (1 : ℚ) + n * ((1 - 1 / (2 * n)) - 1) = 1 / 2 := by
    field_simp
    ring
  rwa [heq] at hbern

/-- INTERNAL: One cooling step bounds each power weight using only the
deficiency bound. No correctness theorem for the paired-rank scan is needed
because natural subtraction already bounds the deficiency by n.
TEXLINE: main.tex:1137-1145 -/
private theorem power_step_bounds (n j d : ℕ) (ρ : ℚ)
    (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1) (hhalf : (1 / 2 : ℚ) ≤ ρ ^ n)
    (hd : d ≤ n) :
    (ρ ^ j) ^ d / 2 ≤ (ρ ^ (j + 1)) ^ d ∧
      (ρ ^ (j + 1)) ^ d ≤ (ρ ^ j) ^ d := by
  have hdhalf : (1 / 2 : ℚ) ≤ ρ ^ d :=
    hhalf.trans (pow_le_pow_of_le_one hρ hρone hd)
  have hdone : ρ ^ d ≤ 1 := pow_le_one₀ hρ hρone
  have hbase : 0 ≤ (ρ ^ j) ^ d := pow_nonneg (pow_nonneg hρ _) _
  rw [pow_succ, mul_pow]
  constructor <;> nlinarith

/-- INTERNAL: Summing the same fixed class at adjacent parameters preserves
the per-state factor-two cooling bounds, including an empty class.
TEXLINE: main.tex:1141-1145 -/
private theorem class_partition_step {α : Type} [Fintype α]
    (n j : ℕ) (ρ : ℚ) (hρ : 0 ≤ ρ) (hρone : ρ ≤ 1)
    (hhalf : (1 / 2 : ℚ) ≤ ρ ^ n) (d : α → ℕ)
    (hd : ∀ a, d a ≤ n) (inClass : α → Prop) [DecidablePred inClass] :
    let Z := fun k => ∑ a, if inClass a then (ρ ^ k) ^ d a else 0
    0 ≤ Z j ∧ Z j / 2 ≤ Z (j + 1) ∧ Z (j + 1) ≤ Z j := by
  classical
  dsimp only
  refine ⟨Finset.sum_nonneg (fun a _ => ?_), ?_, ?_⟩
  · split_ifs <;> positivity
  · rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro a _
    by_cases ha : inClass a
    · simp only [if_pos ha]
      exact (power_step_bounds n j (d a) ρ hρ hρone hhalf (hd a)).1
    · simp [ha]
  · apply Finset.sum_le_sum
    intro a _
    by_cases ha : inClass a
    · simp only [if_pos ha]
      exact (power_step_bounds n j (d a) ρ hρ hρone hhalf (hd a)).2
    · simp [ha]

/-- PAPER: main.tex:1141-1145
Both the transversal partition sum and every ordered defect partition sum
decrease by a factor between one half and one at each schedule step. The
transversal sum is positive; the inequalities also retain empty defect classes. -/
theorem partition_step_bounds (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
    let D := fun a index => FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
    0 < C j ∧ C j / 2 ≤ C (j + 1) ∧ C (j + 1) ≤ C j ∧
      ∀ index, 0 ≤ D j index ∧
        D j index / 2 ≤ D (j + 1) index ∧ D (j + 1) index ≤ D j index := by
  classical
  obtain ⟨hρ, hρone, hhalf⟩ := schedule_power_lower n p hn
  let ρ := (CountingMatroid.Interface.Pseudocode.setup n p).ρ
  have hC := class_partition_step n j ρ hρ.le hρone hhalf
    (TransversalPartition.transversalDeficiency r o₁ o₂)
    (fun _ => Nat.sub_le _ _) (fun _ => True)
  have hCpos : 0 < TransversalPartition.partitionSum r o₁ o₂ (ρ ^ j) := by
    unfold TransversalPartition.partitionSum
    apply Finset.sum_pos
    · intro A _
      exact pow_pos (pow_pos hρ _) _
    · exact Finset.univ_nonempty
  refine ⟨hCpos, ?_, ?_, ?_⟩
  · simpa only [if_true, TransversalPartition.partitionSum] using hC.2.1
  · simpa only [if_true, TransversalPartition.partitionSum] using hC.2.2
  · intro index
    exact class_partition_step n j ρ hρ.le hρone hhalf
      (fun state : PairedSet n => n -
        (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val)
      (fun _ => Nat.sub_le _ _)
      (fun state => (CountingMatroid.Program.classifyState state).val =
        .defect index.emptyPair index.fullPair)

/-- INTERNAL: A quotient of two nonnegative partition sums changes by at
most a factor two when both sums do. The zero-denominator case is retained
and uses Lean's division convention, rather than an unproved class-nonemptiness
claim. TEXLINE: main.tex:1141-1145 -/
private theorem quotient_step_bounds (a b a' b' : ℚ)
    (ha : 0 ≤ a) (hb : 0 ≤ b)
    (ha' : a / 2 ≤ a') (ha'upper : a' ≤ a)
    (hb' : b / 2 ≤ b') (hb'upper : b' ≤ b) :
    (a / b) / 2 ≤ a' / b' ∧ a' / b' ≤ 2 * (a / b) := by
  by_cases hbzero : b = 0
  · have hb'zero : b' = 0 := by rw [hbzero] at hb' hb'upper; linarith
    simp [hbzero, hb'zero]
  · have hbpos : 0 < b := lt_of_le_of_ne hb (Ne.symm hbzero)
    have hb'pos : 0 < b' := (half_pos hbpos).trans_le hb'
    have ha'nonneg : 0 ≤ a' := (div_nonneg ha (by norm_num)).trans ha'
    constructor
    · have hl := div_le_div₀ ha'nonneg ha' hb'pos hb'upper
      have heq : (a / 2) / b = (a / b) / 2 := by ring
      rwa [heq] at hl
    · have hu := div_le_div₀ ha ha'upper (half_pos hbpos) hb'
      have heq : a / (b / 2) = 2 * (a / b) := by field_simp
      rwa [heq] at hu

/-- PAPER: main.tex:1141-1145,1266-1270
The ideal multiplier changes by at most a factor two at the next parameter.
This is proved for the concrete operational partition sums, including n=1
with no defect indices. No concentration estimate is used. -/
theorem ideal_multiplier_drift (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (index : DefectIndex n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let ideal := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a) /
      FirstPhaseFailure.defectPartition r o₁ o₂ (s.ρ ^ a) index
    ideal j / 2 ≤ ideal (j + 1) ∧ ideal (j + 1) ≤ 2 * ideal j := by
  obtain ⟨hC, hClower, hCupper, hD⟩ := partition_step_bounds n r o₁ o₂ p hn j
  obtain ⟨hDnonneg, hDlower, hDupper⟩ := hD index
  exact quotient_step_bounds _ _ _ _ hC.le hDnonneg
    hClower hCupper hDlower hDupper

end CountingMatroid.Analysis.AnnealingPartitionDrift
