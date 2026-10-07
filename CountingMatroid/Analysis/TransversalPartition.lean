import CountingMatroid.Interface.Pseudocode
import CountingMatroid.Analysis.TransversalRankBridge
import CountingMatroid.Analysis.ScheduleConfidence
import Mathlib.Analysis.Complex.ExponentialBounds

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.TransversalPartition

open CountingMatroid.Model

/-- INTERNAL: The paired state corresponding to an original-ground subset;
false marks its selected x elements and true marks its complementary y elements.
TEXLINE: main.tex:270-281 -/
def transversalState {n : ℕ} (A : Finset (Fin n)) : PairedSet n :=
  Finset.univ.image (fun i : Fin n => (i, decide (i ∉ A)))

/-- INTERNAL: Rank deficiency of a transversal, calculated by the same paired
rank scan used by the bounded run.
TEXLINE: main.tex:292-316,1333-1346 -/
noncomputable def transversalDeficiency {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (A : Finset (Fin n)) : ℕ :=
  n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂
    (transversalState A)).val

/-- INTERNAL: The paper's analytical transversal partition sum, expressed over
the concrete rank deficiencies used in `Program.weightOfKind`.
TEXLINE: main.tex:307-316 -/
noncomputable def partitionSum {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) : ℚ :=
  ∑ A : Finset (Fin n), q ^ transversalDeficiency r o₁ o₂ A

/-- INTERNAL: A finite partition sum is controlled by its zero-deficiency
terms and one copy of the weight for each possible term.
TEXLINE: main.tex:1314-1320 -/
private theorem power_sum_contamination_bound {α : Type} [DecidableEq α]
    (s : Finset α) (d : α → ℕ) (q : ℚ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ((s.filter (fun a => d a = 0)).card : ℚ) ≤ ∑ a ∈ s, q ^ d a ∧
      (∑ a ∈ s, q ^ d a) ≤
        ((s.filter (fun a => d a = 0)).card : ℚ) + (s.card : ℚ) * q := by
  have hcount : ((s.filter (fun a => d a = 0)).card : ℚ) =
      ∑ a ∈ s, (if d a = 0 then (1 : ℚ) else 0) := by simp
  constructor
  · rw [hcount]
    apply Finset.sum_le_sum
    intro a ha
    by_cases h : d a = 0
    · simp [h]
    · simp [h, pow_nonneg hq0]
  · rw [hcount]
    calc
      (∑ a ∈ s, q ^ d a) ≤
          ∑ a ∈ s, ((if d a = 0 then (1 : ℚ) else 0) + q) := by
            apply Finset.sum_le_sum
            intro a ha
            by_cases h : d a = 0
            · simp [h, hq0]
            · simp only [if_neg h, zero_add]
              simpa only [pow_one] using
                (pow_le_pow_of_le_one hq0 hq1 (Nat.one_le_iff_ne_zero.mpr h))
      _ = (∑ a ∈ s, if d a = 0 then (1 : ℚ) else 0) + (s.card : ℚ) * q := by
            simp [Finset.sum_add_distrib]

/-- INTERNAL: The positive-ground cooling factor falls by at least a half
over each block of `2n` phases.
TEXLINE: main.tex:1131-1140 -/
private theorem geometric_half (n : ℕ) (hn : 0 < n) :
    (1 - 1 / (2 * (n : ℚ))) ^ (2 * n) ≤ (1 / 2 : ℚ) := by
  have ht : (1 : ℝ) ≤ (2 * n : ℕ) := by
    exact_mod_cast (by omega : 1 ≤ 2 * n)
  have h := Real.one_sub_div_pow_le_exp_neg (n := 2 * n) (t := 1) ht
  have he : Real.exp (-1) ≤ (1 / 2 : ℝ) := Real.exp_neg_one_lt_half.le
  have hc :
      (((1 - 1 / (2 * (n : ℚ))) ^ (2 * n) : ℚ) : ℝ) =
        (1 - 1 / (2 * (n : ℝ))) ^ (2 * n) := by norm_num
  have hden : (2 * (n : ℝ)) = ((2 * n : ℕ) : ℝ) := by norm_num
  have hr : (1 - 1 / (2 * (n : ℝ))) ^ (2 * n) ≤ (1 / 2 : ℝ) := by
    rw [hden]
    exact le_trans h he
  have hr' : (((1 - 1 / (2 * (n : ℚ))) ^ (2 * n) : ℚ) : ℝ) ≤
      (1 / 2 : ℝ) := hc.trans_le hr
  apply (Rat.cast_le (K := ℝ)).mp
  simpa using hr'

/-- INTERNAL: Reuse the public confidence schedule theorem for the same
charged halving search at accuracy threshold `ε/10`.
TEXLINE: main.tex:1105-1115 -/
private theorem accuracy_half_bound (n : ℕ) (p : InputParams) :
    (1 / 2 : ℚ) ^ (CountingMatroid.Program.leastHalvings (p.ε / 10)).val ≤
      p.ε / 10 := by
  let p' : InputParams :=
    { p with
      δ := p.ε / 10
      δ_pos := by exact div_pos p.ε_pos (by norm_num)
      δ_lt_one := by linarith [p.ε_lt_one] }
  have h := (CountingMatroid.Analysis.MedianAmplification.schedule_confidence_bound n p').2
  have hb : (CountingMatroid.Interface.Pseudocode.setup n p').bδ =
      (CountingMatroid.Program.leastHalvings (p.ε / 10)).val := by
    dsimp [CountingMatroid.Interface.Pseudocode.setup,
      CountingMatroid.Program.schedule, p']
  rw [hb] at h
  have heq : (1 / 2 : ENNReal) = ENNReal.ofReal (1 / 2 : ℝ) := by
    rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
    norm_num
  rw [heq, ← ENNReal.ofReal_pow (by positivity)] at h
  have hreal : (1 / 2 : ℝ) ^ (CountingMatroid.Program.leastHalvings (p.ε / 10)).val ≤
      ((p.ε / 10 : ℚ) : ℝ) := by
    have hε : (0 : ℝ) ≤ ((p.ε / 10 : ℚ) : ℝ) := by
      exact_mod_cast (le_of_lt (div_pos p.ε_pos (by norm_num : (0 : ℚ) < 10)))
    exact (ENNReal.ofReal_le_ofReal_iff hε).mp (by simpa [p'] using h)
  apply (Rat.cast_le (K := ℝ)).mp
  simpa using hreal

/-- INTERNAL: At the final schedule parameter, common bases contribute one to
the transversal partition sum and every other transversal contributes at most
`q_L`. The concrete rank scan must agree with matroid rank for this comparison.
TEXLINE: main.tex:1314-1323 -/
theorem transversal_partition_contamination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let c := partitionSum r o₁ o₂ (s.ρ ^ s.L)
    (commonBaseCount M₁ M₂ : ℚ) ≤ c ∧
      c ≤ (1 + p.ε / 10) * (commonBaseCount M₁ M₂ : ℚ) := by
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
  have hL : (CountingMatroid.Interface.Pseudocode.setup n p).L =
      2 * n * (n + (CountingMatroid.Program.leastHalvings (p.ε / 10)).val) := by
    simp only [CountingMatroid.Interface.Pseudocode.setup,
      CountingMatroid.Program.schedule, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure,
      CountingMatroid.Model.Operations.ratDiv,
      CountingMatroid.Model.Operations.ratSub,
      CountingMatroid.Model.Operations.ratOfNat,
      CountingMatroid.Model.Operations.natMul,
      CountingMatroid.Model.Operations.natAdd,
      Arlib.Computation.Charged.val_op,
      Arlib.Computation.Charged.val_opMany]
  have hρrange :
      0 ≤ (CountingMatroid.Interface.Pseudocode.setup n p).ρ ∧
        (CountingMatroid.Interface.Pseudocode.setup n p).ρ ≤ 1 := by
    rw [hρ]
    by_cases hn : n = 0
    · subst n
      norm_num
    · have hnpos : (0 : ℚ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
      have hn1 : (1 : ℚ) ≤ n := by
        exact_mod_cast Nat.one_le_iff_ne_zero.mpr hn
      have hden : (0 : ℚ) < 2 * n := by positivity
      have hdiv : 0 ≤ (1 : ℚ) / (2 * n) ∧ (1 : ℚ) / (2 * n) ≤ 1 := by
        constructor
        · positivity
        · apply (div_le_iff₀ hden).2
          nlinarith
      constructor <;> linarith
  have hqrange :
      0 ≤ (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup n p).L ∧
        (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup n p).L ≤ 1 := by
    constructor
    · exact pow_nonneg hρrange.1 _
    · calc
        _ ≤ (1 : ℚ) ^ (CountingMatroid.Interface.Pseudocode.setup n p).L :=
          pow_le_pow_left₀ hρrange.1 hρrange.2 _
        _ = 1 := by simp
  have hsum := power_sum_contamination_bound
    (Finset.univ : Finset (Finset (Fin n)))
    (transversalDeficiency r o₁ o₂)
    ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
      (CountingMatroid.Interface.Pseudocode.setup n p).L)
    hqrange.1 hqrange.2
  have hcard : ((Finset.univ : Finset (Finset (Fin n))).card : ℚ) =
      (2 : ℚ) ^ n := by
    simp [Fintype.card_finset]
  have hzero :
      (Finset.univ : Finset (Finset (Fin n))).filter
        (fun A => transversalDeficiency r o₁ o₂ A = 0) =
      commonBases M₁ M₂ := by
    ext A
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact TransversalRankBridge.transversal_rank_zero_iff_common_base
      n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂ A
  have hcount :
      (((Finset.univ : Finset (Finset (Fin n))).filter
        (fun A => transversalDeficiency r o₁ o₂ A = 0)).card : ℚ) =
      (commonBaseCount M₁ M₂ : ℚ) := by
    rw [hzero]
    rfl
  have htail (hn : 0 < n) :
      (2 : ℚ) ^ n * (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
        (CountingMatroid.Interface.Pseudocode.setup n p).L ≤ p.ε / 10 := by
    rw [hρ, hL]
    let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
    let ρ : ℚ := 1 - 1 / (2 * (n : ℚ))
    have hbase : 0 ≤ ρ ^ (2 * n) := by
      change 0 ≤ (1 - 1 / (2 * (n : ℚ))) ^ (2 * n)
      rw [← hρ]
      exact pow_nonneg hρrange.1 _
    have hblock : ρ ^ (2 * n) ≤ (1 / 2 : ℚ) := geometric_half n hn
    have hpow : (ρ ^ (2 * n)) ^ (n + b) ≤
        (1 / 2 : ℚ) ^ (n + b) :=
      pow_le_pow_left₀ hbase hblock _
    calc
      (2 : ℚ) ^ n * ρ ^ (2 * n * (n + b)) =
          (2 : ℚ) ^ n * (ρ ^ (2 * n)) ^ (n + b) := by rw [pow_mul]
      _ ≤ (2 : ℚ) ^ n * (1 / 2 : ℚ) ^ (n + b) := by
        exact mul_le_mul_of_nonneg_left hpow (by positivity)
      _ = (1 / 2 : ℚ) ^ b := by
        rw [pow_add, ← mul_assoc, ← mul_pow]
        norm_num
      _ ≤ p.ε / 10 := accuracy_half_bound n p
  by_cases hn : n = 0
  · subst n
    classical
    have hU : (Finset.univ : Finset (Finset (Fin 0))) = {∅} := by decide
    have hZle : commonBaseCount M₁ M₂ ≤ 1 := by
      unfold commonBaseCount commonBases
      have hsub : (Finset.univ.filter
          (fun B : Finset (Fin 0) =>
            M₁.IsBase (B : Set (Fin 0)) ∧ M₂.IsBase (B : Set (Fin 0)))) ⊆
          (Finset.univ : Finset (Finset (Fin 0))) := Finset.filter_subset _ _
      have hc := Finset.card_le_card hsub
      simpa only [hU, Finset.card_singleton] using hc
    have hZ1 : commonBaseCount M₁ M₂ = 1 := by omega
    have hbase : (∅ : Finset (Fin 0)) ∈ commonBases M₁ M₂ := by
      have hne : (commonBases M₁ M₂).Nonempty := by
        exact Finset.card_pos.mp (show 0 < (commonBases M₁ M₂).card from hpositive)
      obtain ⟨A, hA⟩ := hne
      have he : A = ∅ := by ext i; exact Fin.elim0 i
      simpa only [he] using hA
    have hdef : transversalDeficiency r o₁ o₂ (∅ : Finset (Fin 0)) = 0 := by
      exact (TransversalRankBridge.transversal_rank_zero_iff_common_base
        0 r M₁ M₂ o₁ o₂ hfull hr h₁ h₂ ∅).2 hbase
    have hc : partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup 0 p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup 0 p).L) = 1 := by
      unfold partitionSum
      rw [hU]
      simp only [Finset.sum_singleton, hdef, pow_zero]
    change (commonBaseCount M₁ M₂ : ℚ) ≤
      partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup 0 p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup 0 p).L) ∧
      partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup 0 p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup 0 p).L) ≤
        (1 + p.ε / 10) * (commonBaseCount M₁ M₂ : ℚ)
    rw [hZ1, hc]
    constructor
    · norm_num
    · have hε : (0 : ℚ) ≤ p.ε / 10 :=
        le_of_lt (div_pos p.ε_pos (by norm_num))
      nlinarith
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    have hc : (commonBaseCount M₁ M₂ : ℚ) ≤
        partitionSum r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
            (CountingMatroid.Interface.Pseudocode.setup n p).L) ∧
        partitionSum r o₁ o₂
          ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
            (CountingMatroid.Interface.Pseudocode.setup n p).L) ≤
          (commonBaseCount M₁ M₂ : ℚ) +
            (2 : ℚ) ^ n *
              (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
                (CountingMatroid.Interface.Pseudocode.setup n p).L := by
      simpa only [partitionSum, hcount, hcard] using hsum
    have hZ : (1 : ℚ) ≤ (commonBaseCount M₁ M₂ : ℚ) := by
      exact_mod_cast hpositive
    have hε : (0 : ℚ) ≤ p.ε / 10 :=
      le_of_lt (div_pos p.ε_pos (by norm_num))
    have hm : 0 ≤ (p.ε / 10) * ((commonBaseCount M₁ M₂ : ℚ) - 1) :=
      mul_nonneg hε (sub_nonneg.mpr hZ)
    change (commonBaseCount M₁ M₂ : ℚ) ≤
      partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup n p).L) ∧
      partitionSum r o₁ o₂
        ((CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup n p).L) ≤
        (1 + p.ε / 10) * (commonBaseCount M₁ M₂ : ℚ)
    constructor
    · exact hc.1
    · calc
        _ ≤ (commonBaseCount M₁ M₂ : ℚ) +
            (2 : ℚ) ^ n *
              (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^
                (CountingMatroid.Interface.Pseudocode.setup n p).L := hc.2
        _ ≤ (commonBaseCount M₁ M₂ : ℚ) + p.ε / 10 := by
          simpa only [add_comm] using
            (add_le_add_left (htail hnpos) (commonBaseCount M₁ M₂ : ℚ))
        _ ≤ (1 + p.ε / 10) * (commonBaseCount M₁ M₂ : ℚ) := by
          nlinarith

end CountingMatroid.Analysis.TransversalPartition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r10 · conditional · closed the contamination calculation for all n using a new rank-scan bridge; the bridge still has a `sorry` and its requested scheduler handoff was refused.
* r9 · partial · proved the generic power-sum comparison, nonnegative schedule weight, and exact schedule field identities; rank-scan correctness and the final tail estimate remain open.
* r8 · open · direct simplification exposes the missing paired-rank correctness theorem and the final schedule tail bound.
-/
