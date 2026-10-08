import CountingMatroid.Analysis.ScheduleThermalSetupCost
import CountingMatroid.Analysis.ScheduleCostPrimitives

/-!
# Cost of the schedule tail

The setup phases have separate checked cost bounds. This module proves an exact
cost identity for the charged powers, observation count, draw width, and confidence
repetition computation, and bounds their sum by the prescribed polynomial.
Intermediate encoding lengths are bounded using the shared length and capped-search
lemmas in `ScheduleCostPrimitives`.
-/

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Expand the schedule tail into its four power computations,
unit word charges, rational operations, and two capped searches.
TEXLINE: main.tex:1348-1358 -/
theorem thermalRest_cost_eq (n : ℕ) (p : InputParams) (t : ThermalResult) :
    let A := 10000000000 * t.LPlusOne * (CountingMatroid.Program.natPower n 14).val
    let R := 2000 * (CountingMatroid.Program.natPower t.LPlusOne 2).val *
      (CountingMatroid.Program.natPower n 2).val *
      (20 * (CountingMatroid.Program.natPower n 4).val * (n * t.LPlusOne + 2))
    let Q := (A : ℚ) / (t.eta * t.eta)
    otherSteps (thermalRest n p t) =
      otherSteps (CountingMatroid.Program.natPower n 4) +
      otherSteps (CountingMatroid.Program.natPower t.LPlusOne 2) +
      otherSteps (CountingMatroid.Program.natPower n 2) +
      otherSteps (CountingMatroid.Program.natPower n 14) + 14 + (A.log2 + 1) +
      otherSteps (CountingMatroid.Model.Operations.ratMul t.eta t.eta) +
      otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (t.eta * t.eta)) +
      otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) +
      otherSteps (CountingMatroid.Program.leastDrawTrials
        (3 * t.L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) +
      otherSteps (CountingMatroid.Program.leastHalvings p.δ) := by
  have hop {α : Type} (i : Arlib.Computation.Op) (x : α) :
      otherSteps (Arlib.Computation.Charged.op
        (CountingMatroid.Model.Operations.Op.word i) x) = 1 := by
    cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.one]
  have hcast (a : ℕ) :
      otherSteps (CountingMatroid.Model.Operations.ratOfNat a) = a.log2 + 1 := by
    simp [CountingMatroid.Model.Operations.ratOfNat, otherSteps,
      Arlib.Computation.Op.all, Arlib.Computation.CostVec.many]
  have hpure (x : AnnealingSchedule) :
      otherSteps (pure x : Arlib.Computation.Charged
        CountingMatroid.Model.Operations.Op CountingMatroid.Model.Operations.Cell
        AnnealingSchedule) = 0 := by simp [otherSteps]
  dsimp only
  unfold thermalRest
  simp only [CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
  simp only [CountingMatroid.Model.Operations.natAdd,
    CountingMatroid.Model.Operations.natMul, CountingMatroid.Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hop, hcast, hpure]
  simp only [CountingMatroid.Model.Operations.ratOfNat,
    CountingMatroid.Model.Operations.ratMul, CountingMatroid.Model.Operations.ratDiv,
    Arlib.Computation.Charged.val_opMany]
  omega

/-- INTERNAL: The remaining charged schedule operations have a polynomial
nonoracle charge after the opening and thermal setup phases.
TEXLINE: main.tex:1348-1358 -/
theorem thermalRest_otherSteps_poly (n r : ℕ) (p : InputParams) :
    let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
      binaryNatLength (Nat.ceil p.δ⁻¹) + 1
    let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
    let L := 2 * n * (n + b)
    let D := 32 * (L + 1)
    otherSteps (thermalRest n p
      ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, p.ε / (D : ℚ)⟩) ≤
      10 ^ 150 * S ^ 40 := by
  have hceil_cost (q : ℚ) : otherSteps (CountingMatroid.Model.Operations.rationalCeil q) =
      (q.num.natAbs.log2 + q.den.log2 + 3) ^ 2 := by
    simp [CountingMatroid.Model.Operations.rationalCeil, otherSteps,
      Arlib.Computation.Op.all, Arlib.Computation.CostVec.many]
    rfl
  have hpowlog (base exponent : ℕ) :
      (CountingMatroid.Program.natPower base exponent).val.log2 ≤
        exponent * (base.log2 + 1) := by
    have hfold (l : List ℕ) (acc : ℕ) :
        (Arlib.Computation.Charged.foldl
          (fun acc _ => CountingMatroid.Model.Operations.natMul acc base) l acc).val.log2 ≤
          acc.log2 + l.length * (base.log2 + 1) := by
      induction l generalizing acc with
      | nil => simp
      | cons x xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        have h := ih (acc * base)
        have hm := log2_mul_le acc base
        simpa only [CountingMatroid.Model.Operations.natMul,
          Arlib.Computation.Charged.val_op, List.length_cons] using
          (h.trans (by nlinarith :
            (acc * base).log2 + xs.length * (base.log2 + 1) ≤
              acc.log2 + (xs.length + 1) * (base.log2 + 1)))
    simpa [CountingMatroid.Program.natPower, Arlib.Computation.Charged.repeatFor,
      show (1 : ℕ).log2 = 0 from rfl]
      using hfold (List.range exponent) 1
  let S := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
    binaryNatLength (Nat.ceil p.δ⁻¹) + 1
  let X := S ^ 2
  let b := (CountingMatroid.Program.leastHalvings (p.ε / 10)).val
  let L := 2 * n * (n + b)
  let D := 32 * (L + 1)
  let eta := p.ε / (D : ℚ)
  let A := 10000000000 * (L + 1) * (CountingMatroid.Program.natPower n 14).val
  let R := 2000 * (CountingMatroid.Program.natPower (L + 1) 2).val *
    (CountingMatroid.Program.natPower n 2).val *
    (20 * (CountingMatroid.Program.natPower n 4).val * (n * (L + 1) + 2))
  let Q := (A : ℚ) / (eta * eta)
  have hS : 1 ≤ S := by dsimp [S]; omega
  have hn : n ≤ S := by dsimp [S]; omega
  have he : binaryRatLength p.ε ≤ S := by dsimp [S, binaryInputLength]; omega
  have hd : binaryRatLength p.δ ≤ S := by dsimp [S, binaryInputLength]; omega
  have hSX : S ≤ X := by dsimp [X]; nlinarith
  have hX : 1 ≤ X := by omega
  have hlog (a : ℕ) : a.log2 ≤ a := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 a
  have hb : b ≤ S + 15 := by
    have h := leastHalvings_value_le (p.ε / 10)
    have hlen := binaryRatLength_div_le p.ε 10
    have hten : binaryRatLength (10 : ℚ) = 7 := by decide
    rw [hten] at hlen
    dsimp [b]
    unfold binaryRatLength binaryNatLength at he hlen
    omega
  have hL : L ≤ 34 * X := by
    have hnb : n + b ≤ 17 * S := by omega
    calc
      L ≤ (2 * S) * (17 * S) :=
        Nat.mul_le_mul (Nat.mul_le_mul_left 2 hn) hnb
      _ = 34 * X := by dsimp [X]; ring
  have hL1 : (L + 1).log2 ≤ 35 * X := by have := hlog (L + 1); omega
  have hLl : L.log2 ≤ 34 * X := (hlog L).trans hL
  have hDl : D.log2 ≤ 1120 * X := by
    have := hlog D
    dsimp [D] at this ⊢
    omega
  have hnl : n.log2 ≤ X := (hlog n).trans (hn.trans hSX)
  have hAl : A.log2 ≤ 100 * X := by
    have h1 := log2_mul_le 10000000000 (L + 1)
    have h2 := log2_mul_le (10000000000 * (L + 1))
      (CountingMatroid.Program.natPower n 14).val
    have hp := hpowlog n 14
    have hc : (10000000000 : ℕ).log2 = 33 := by decide
    dsimp [A]
    omega
  have hRl : R.log2 ≤ 150 * X := by
    have h1 := log2_mul_le 2000 (CountingMatroid.Program.natPower (L + 1) 2).val
    have h2 := log2_mul_le
      (2000 * (CountingMatroid.Program.natPower (L + 1) 2).val)
      (CountingMatroid.Program.natPower n 2).val
    have h3 := log2_mul_le 20 (CountingMatroid.Program.natPower n 4).val
    have h4 := log2_mul_le n (L + 1)
    have h5 := log2_add_le (n * (L + 1)) 2
    have h6 := log2_mul_le (20 * (CountingMatroid.Program.natPower n 4).val)
      (n * (L + 1) + 2)
    have h7 := log2_mul_le
      (2000 * (CountingMatroid.Program.natPower (L + 1) 2).val *
        (CountingMatroid.Program.natPower n 2).val)
      (20 * (CountingMatroid.Program.natPower n 4).val * (n * (L + 1) + 2))
    have hp1 := hpowlog (L + 1) 2
    have hp2 := hpowlog n 2
    have hp4 := hpowlog n 4
    have hc1 : (2000 : ℕ).log2 = 10 := by decide
    have hc2 : (20 : ℕ).log2 = 4 := by decide
    have hc3 : (2 : ℕ).log2 = 1 := by decide
    dsimp [R]
    omega
  have heta : binaryRatLength eta ≤ 1125 * X := by
    have h := binaryRatLength_div_le p.ε (D : ℚ)
    rw [binaryRatLength_natCast] at h
    dsimp [eta]
    omega
  have heta2 : binaryRatLength (eta * eta) ≤ 2250 * X := by
    have := binaryRatLength_mul_le eta eta
    omega
  have hQ : binaryRatLength Q ≤ 2400 * X := by
    have := observationQuotient_length_le A D p.ε
    dsimp [Q, eta]
    omega
  have hdrawLog : (3 * L *
      (R + (CountingMatroid.Model.Operations.rationalCeil Q).val)).log2 ≤ 2600 * X := by
    have h1 := log2_mul_le 3 L
    have h2 := log2_add_le R (CountingMatroid.Model.Operations.rationalCeil Q).val
    have h3 := log2_mul_le (3 * L)
      (R + (CountingMatroid.Model.Operations.rationalCeil Q).val)
    have h4 := rationalCeil_log2_le Q
    have hc : (3 : ℕ).log2 = 1 := by decide
    omega
  have hmul : otherSteps (CountingMatroid.Model.Operations.ratMul eta eta) ≤
      9000000 * S ^ 4 := by
    have h := rationalBinary_otherSteps_le .mul eta eta (eta * eta)
    have hs : (binaryRatLength eta + binaryRatLength eta) ^ 2 ≤ (3000 * X) ^ 2 :=
      Nat.pow_le_pow_left (by omega) 2
    have heq : (3000 * X) ^ 2 = 9000000 * S ^ 4 := by dsimp [X]; ring
    exact h.trans (hs.trans_eq heq)
  have hdiv : otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (eta * eta)) ≤
      9000000 * S ^ 4 := by
    have h := rationalBinary_otherSteps_le .udiv (A : ℚ) (eta * eta) Q
    have hlen : binaryRatLength (A : ℚ) + binaryRatLength (eta * eta) ≤ 3000 * X := by
      rw [binaryRatLength_natCast]
      omega
    have hs := Nat.pow_le_pow_left hlen 2
    have heq : (3000 * X) ^ 2 = 9000000 * S ^ 4 := by dsimp [X]; ring
    exact h.trans (hs.trans_eq heq)
  have hceil : otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) ≤
      9000000 * S ^ 4 := by
    rw [hceil_cost]
    have hlen : Q.num.natAbs.log2 + Q.den.log2 + 3 ≤ 3000 * X := by
      unfold binaryRatLength binaryNatLength at hQ
      omega
    calc
      _ ≤ (3000 * X) ^ 2 := Nat.pow_le_pow_left hlen 2
      _ = 9000000 * S ^ 4 := by dsimp [X]; ring
  have hdraw : otherSteps (CountingMatroid.Program.leastDrawTrials
      (3 * L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) ≤
        8000 * X := by
    have := leastDrawTrials_otherSteps_le
      (3 * L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))
    omega
  have hdelta : otherSteps (CountingMatroid.Program.leastHalvings p.δ) ≤
      300000 * S ^ 4 := by
    have hden : p.δ.den.log2 ≤ S := by
      unfold binaryRatLength binaryNatLength at hd
      omega
    have h := LeastHalvingsCost.leastHalvings_otherSteps_le p.δ
    have h1 : p.δ.den.log2 + 8 ≤ 9 * S := by omega
    have h2 : binaryRatLength p.δ + p.δ.den.log2 + 16 ≤ 18 * S := by omega
    have hprod := Nat.mul_le_mul (Nat.mul_le_mul_left 100 h1)
      (Nat.pow_le_pow_left h2 2)
    have heq : 100 * (9 * S) * (18 * S) ^ 2 = 291600 * S ^ 3 := by ring
    rw [heq] at hprod
    have h34 : S ^ 3 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide)
    have h4 : 1 ≤ S ^ 4 := one_le_pow₀ hS
    omega
  change otherSteps (thermalRest n p
    ⟨⟨b, 1 - 1 / (2 * n : ℚ), 2 * n⟩, L, L + 1, D, eta⟩) ≤
      10 ^ 150 * S ^ 40
  rw [thermalRest_cost_eq]
  simp only [natPower_otherSteps_eq]
  change 4 + 2 + 2 + 14 + 14 + (A.log2 + 1) +
    otherSteps (CountingMatroid.Model.Operations.ratMul eta eta) +
    otherSteps (CountingMatroid.Model.Operations.ratDiv (A : ℚ) (eta * eta)) +
    otherSteps (CountingMatroid.Model.Operations.rationalCeil Q) +
    otherSteps (CountingMatroid.Program.leastDrawTrials
      (3 * L * (R + (CountingMatroid.Model.Operations.rationalCeil Q).val))) +
    otherSteps (CountingMatroid.Program.leastHalvings p.δ) ≤ 10 ^ 150 * S ^ 40
  have hX40 : X ≤ S ^ 40 := pow_le_pow_right₀ hS (by decide)
  have h440 : S ^ 4 ≤ S ^ 40 := pow_le_pow_right₀ hS (by decide)
  have h40 : 1 ≤ S ^ 40 := one_le_pow₀ hS
  omega

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · proved · closed thermalRest_otherSteps_poly using quadratic encoding-length
  bounds and the shared primitive cost estimates; no new proof obligations.

* r16 · blocked · confirmed the downstream helper placement with an import-only
  Lean probe and source search; requested a shared ScheduleCostPrimitives module
  with public power and rational-operation cost bounds. No proof debt moved.
* r15 · partial · proved thermalRest_cost_eq and applied it in the target;
  the existing rational-length and capped-search helpers are downstream of
  the target, requiring extraction to a shared module before reuse.
-/
