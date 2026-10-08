import CountingMatroid.Analysis.ScheduleOpeningCost
set_option autoImplicit false
open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
/-- INTERNAL: Values passed from the thermal setup to the schedule tail. -/
structure ThermalResult where
  opening : ScheduleOpeningResult
  L : ℕ
  LPlusOne : ℕ
  D : ℕ
  eta : ℚ
/-- INTERNAL: The charged setup of phase count and annealing accuracy.
TEXLINE: main.tex:1348-1358 -/
def thermalSetup (n : ℕ) (p : InputParams) (head : ScheduleOpeningResult) :
    Arlib.Computation.Charged Op Cell ThermalResult := do
  let nPlusB ← natAdd n head.bε
  let L ← natMul head.twoN nPlusB
  let LPlusOne ← successor L
  let D ← natMul 32 LPlusOne
  let etaDen ← ratOfNat D
  let eta ← ratDiv p.ε etaDen
  pure ⟨head, L, LPlusOne, D, eta⟩
/-- INTERNAL: The schedule tail after thermal setup.
TEXLINE: main.tex:1348-1358 -/
def thermalRest (n : ℕ) (p : InputParams) (result : ThermalResult) :
    Arlib.Computation.Charged Op Cell AnnealingSchedule := do
  let b := result.opening.bε
  let rho := result.opening.rho
  let L := result.L
  let eta := result.eta
  let LPlusOne := result.LPlusOne
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
/-- INTERNAL: The opening remainder splits exactly at the thermal setup.
TEXLINE: main.tex:1348-1358 -/
theorem scheduleRemaining_split (n : ℕ) (p : InputParams) (head : ScheduleOpeningResult) :
    scheduleRemaining n p head = thermalSetup n p head >>= thermalRest n p := by
  simp only [scheduleRemaining, thermalSetup, thermalRest, bind_assoc, pure_bind]
/-- INTERNAL: One charged word operation contributes one nonoracle step. -/
private theorem wordOp_cost {α : Type} (instr : Arlib.Computation.Op) (x : α) :
    otherSteps (Arlib.Computation.Charged.op (Op.word instr) x) = 1 := by
  cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.one]

/-- INTERNAL: A charged batch of word operations contributes its batch size. -/
private theorem wordMany_cost {α : Type} (instr : Arlib.Computation.Op)
    (z : ℕ) (x : α) :
    otherSteps (Arlib.Computation.Charged.opMany (Op.word instr) z x) = z := by
  cases instr <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.many]

/-- INTERNAL: Returning a value contributes no charge. -/
private theorem pure_cost {α : Type} (x : α) :
    otherSteps (pure x : Arlib.Computation.Charged Op Cell α) = 0 := by
  simp [otherSteps]

/-- INTERNAL: Thermal setup returns the phase count, its successor,
the accuracy denominator, and the resulting accuracy. -/
theorem thermalSetup_value (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    let L := head.twoN * (n + head.bε)
    let D := 32 * (L + 1)
    (thermalSetup n p head).val =
      ⟨head, L, L + 1, D, p.ε / (D : ℚ)⟩ := by
  dsimp only
  simp [thermalSetup, natAdd, natMul, successor, ratOfNat, ratDiv]

/-- INTERNAL: Thermal setup has four unit word charges, one natural cast,
and one rational division. -/
theorem thermalSetup_cost_eq (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    otherSteps (thermalSetup n p head) =
      4 + (32 * (head.twoN * (n + head.bε) + 1)).log2 + 1 +
        otherSteps (ratDiv p.ε
          (32 * (head.twoN * (n + head.bε) + 1) : ℚ)) := by
  unfold thermalSetup
  simp only [CountingMatroid.Analysis.ResourceBound.otherSteps_bind]
  simp only [natAdd, natMul, successor, ratOfNat,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany]
  simp only [wordOp_cost, wordMany_cost]
  simp only [pure_cost, Nat.add_zero]
  norm_num [Nat.cast_mul, Nat.cast_add]
  omega


/-- INTERNAL: Thermal setup cost is controlled by its denominator length. -/
theorem thermalSetup_otherSteps_le (n : ℕ) (p : InputParams)
    (head : ScheduleOpeningResult) :
    let D := 32 * (head.twoN * (n + head.bε) + 1)
    otherSteps (thermalSetup n p head) ≤
      5 + D.log2 + (binaryRatLength p.ε + binaryRatLength (D : ℚ)) ^ 2 := by
  dsimp only
  rw [thermalSetup_cost_eq]
  have h := opening_rationalBinary_cost_le Arlib.Computation.Op.udiv
    p.ε (32 * (head.twoN * (n + head.bε) + 1) : ℚ)
    (p.ε / (32 * (head.twoN * (n + head.bε) + 1) : ℚ))
  change otherSteps (ratDiv p.ε
    (32 * (head.twoN * (n + head.bε) + 1) : ℚ)) ≤
    (binaryRatLength p.ε +
      binaryRatLength (32 * (head.twoN * (n + head.bε) + 1) : ℚ)) ^ 2 at h
  norm_num [Nat.cast_mul, Nat.cast_add] at h ⊢
  omega

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
