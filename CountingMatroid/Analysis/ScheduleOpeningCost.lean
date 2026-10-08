import CountingMatroid.Analysis.LeastHalvingsCost
set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
/-- INTERNAL: Values passed from the first six charged schedule operations. -/
structure ScheduleOpeningResult where
  bε : ℕ
  rho : ℚ
  twoN : ℕ
/-- INTERNAL: The initial accuracy search and inverse-temperature setup.
TEXLINE: main.tex:1348-1351 -/
def scheduleOpening (n : ℕ) (p : InputParams) :
    Arlib.Computation.Charged Op Cell ScheduleOpeningResult := do
  let epsilonTenth ← ratDiv p.ε 10
  let bε ← CountingMatroid.Program.leastHalvings epsilonTenth
  let twoN ← natMul 2 n
  let twoNq ← ratOfNat twoN
  let inverseTwoN ← ratDiv 1 twoNq
  let rho ← ratSub 1 inverseTwoN
  pure ⟨bε, rho, twoN⟩
/-- INTERNAL: The remainder of the schedule after its first six operations.
TEXLINE: main.tex:1348-1358 -/
def scheduleRemaining (n : ℕ) (p : InputParams) (head : ScheduleOpeningResult) :
    Arlib.Computation.Charged Op Cell AnnealingSchedule := do
  let b := head.bε
  let rho := head.rho
  let twoN := head.twoN
  let nPlusB ← natAdd n b
  let L ← natMul twoN nPlusB
  let LPlusOne ← successor L
  let etaDenNat ← natMul 32 LPlusOne
  let etaDen ← ratOfNat etaDenNat
  let eta ← ratDiv p.ε etaDen
  let nFourth ← CountingMatroid.Program.natPower n 4
  let nTimesL ← natMul n LPlusOne
  let traceInner ← natAdd nTimesL 2
  let traceScale ← natMul 20 nFourth
  let tau ← natMul traceScale traceInner
  let LSquare ← CountingMatroid.Program.natPower LPlusOne 2
  let nSquare ← CountingMatroid.Program.natPower n 2
  let restartFactor ← natMul 2000 LSquare
  let restartFactor ← natMul restartFactor nSquare
  let restartCap ← natMul restartFactor tau
  let nFourteenth ← CountingMatroid.Program.natPower n 14
  let observationFactor ← natMul 10000000000 LPlusOne
  let observationFactor ← natMul observationFactor nFourteenth
  let observationNumerator ← ratOfNat observationFactor
  let etaSquare ← ratMul eta eta
  let observationQuotient ← ratDiv observationNumerator etaSquare
  let observations ← rationalCeil observationQuotient
  let attemptsAndObservations ← natAdd restartCap observations
  let threeL ← natMul 3 L
  let drawCalls ← natMul threeL attemptsAndObservations
  let drawTrials ← CountingMatroid.Program.leastDrawTrials drawCalls
  let bδ ← CountingMatroid.Program.leastHalvings p.δ
  let tenBδ ← natMul 10 bδ
  let repetitions ← successor tenBδ
  pure (AnnealingSchedule.mk b rho L eta tau restartCap observations
    drawCalls drawTrials bδ repetitions)
/-- INTERNAL: The source schedule is exactly its opening followed by its remainder.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_split (n : ℕ) (p : InputParams) :
    CountingMatroid.Program.schedule n p = scheduleOpening n p >>= scheduleRemaining n p := by
  simp only [CountingMatroid.Program.schedule, scheduleOpening, scheduleRemaining, bind_assoc, pure_bind]
/-- INTERNAL: The opening computation produces the values used by the
remaining schedule operations. -/
theorem scheduleOpening_value (n : ℕ) (p : InputParams) :
    (scheduleOpening n p).val =
      ⟨(CountingMatroid.Program.leastHalvings (p.ε / 10)).val,
        1 - 1 / (2 * n : ℚ), 2 * n⟩ := by
  simp [scheduleOpening, ratDiv, ratSub, natMul, ratOfNat]

/-- INTERNAL: The opening schedule cost separates the halving search from
its five primitive operations. -/
theorem scheduleOpening_cost_eq (n : ℕ) (p : InputParams) :
    otherSteps (scheduleOpening n p) =
      otherSteps (ratDiv p.ε 10) +
      otherSteps (CountingMatroid.Program.leastHalvings (p.ε / 10)) +
      otherSteps (natMul 2 n) +
      otherSteps (ratOfNat (2 * n)) +
      otherSteps (ratDiv 1 (2 * n : ℚ)) +
      otherSteps (ratSub 1 (1 / (2 * n : ℚ))) := by
  unfold scheduleOpening
  simp only [CountingMatroid.Analysis.ResourceBound.otherSteps_bind,
    ]
  simp only [ratDiv, natMul, ratOfNat, ratSub,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany]
  simp [otherSteps, Nat.add_assoc]

/-- INTERNAL: A charged rational binary operation is bounded by the
binary lengths of its inputs. -/
theorem opening_rationalBinary_cost_le (instr : Arlib.Computation.Op)
    (a b result : ℚ) :
    otherSteps (Arlib.Computation.Charged.opMany
      (Op.word instr)
      ((a.num.natAbs.log2 + a.den.log2 + 3 +
        (b.num.natAbs.log2 + b.den.log2 + 3)) ^ 2) result) ≤
      (binaryRatLength a + binaryRatLength b) ^ 2 := by
  have hcost (z : ℕ) : otherSteps
      (Arlib.Computation.Charged.opMany (Op.word instr) z result) = z := by
    cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  rw [hcost]
  unfold binaryRatLength binaryNatLength
  apply Nat.pow_le_pow_left
  omega

/-- INTERNAL: The opening cost is the capped halving search plus five
primitive charges bounded by their operand lengths. -/
theorem scheduleOpening_otherSteps_le (n : ℕ) (p : InputParams) :
    otherSteps (scheduleOpening n p) ≤
      (binaryRatLength p.ε + 7) ^ 2 +
      otherSteps (CountingMatroid.Program.leastHalvings (p.ε / 10)) +
      1 + ((2 * n).log2 + 1) +
      (4 + binaryRatLength (2 * n : ℚ)) ^ 2 +
      (4 + binaryRatLength (1 / (2 * n : ℚ))) ^ 2 := by
  rw [scheduleOpening_cost_eq]
  have hten : binaryRatLength (10 : ℚ) = 7 := by decide
  have hone : binaryRatLength (1 : ℚ) = 4 := by decide
  have hdiv := opening_rationalBinary_cost_le Arlib.Computation.Op.udiv
    p.ε 10 (p.ε / 10)
  have hinv := opening_rationalBinary_cost_le Arlib.Computation.Op.udiv
    1 (2 * n : ℚ) (1 / (2 * n : ℚ))
  have hsub := opening_rationalBinary_cost_le Arlib.Computation.Op.sub
    1 (1 / (2 * n : ℚ)) (1 - 1 / (2 * n : ℚ))
  have hmul : otherSteps (natMul 2 n) = 1 := by
    simp [otherSteps, natMul, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.one]
  have hcast : otherSteps (ratOfNat (2 * n)) = (2 * n).log2 + 1 := by
    simp [otherSteps, ratOfNat, Arlib.Computation.Op.all,
      Arlib.Computation.CostVec.many]
  change otherSteps (ratDiv p.ε 10) ≤
    (binaryRatLength p.ε + binaryRatLength (10 : ℚ)) ^ 2 at hdiv
  change otherSteps (ratDiv 1 (2 * n : ℚ)) ≤
    (binaryRatLength (1 : ℚ) + binaryRatLength (2 * n : ℚ)) ^ 2 at hinv
  change otherSteps (ratSub 1 (1 / (2 * n : ℚ))) ≤
    (binaryRatLength (1 : ℚ) +
      binaryRatLength (1 / (2 * n : ℚ))) ^ 2 at hsub
  rw [hten] at hdiv
  rw [hone] at hinv hsub
  omega

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
