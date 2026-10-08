import CountingMatroid.Model.Run
import CountingMatroid.Analysis.LeastHalvingsCost
import CountingMatroid.Analysis.ScheduleOpeningCost
import CountingMatroid.Analysis.ScheduleThermalSetupCost
import CountingMatroid.Analysis.ScheduleThermalRestCost
import CountingMatroid.Analysis.ScheduleCostPrimitives

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

open CountingMatroid.Analysis.ResourceBound (otherSteps_bind)

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
