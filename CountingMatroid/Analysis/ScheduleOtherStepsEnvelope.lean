import CountingMatroid.Model.Run
import CountingMatroid.Analysis.LeastHalvingsCost

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The nonoracle charge is additive under charged sequencing. -/
private theorem otherSteps_bind {α β : Type}
    (q : Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell α)
    (f : α → Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
      CountingMatroid.Model.Operations.Cell β) :
    otherSteps (q >>= f) = otherSteps q + otherSteps (f q.val) := by
  have fold_add (l : List Arlib.Computation.Op)
      (u v : Arlib.Computation.Op → ℕ) (a b : ℕ) :
      l.foldl (fun z x => z + (u x + v x)) (a + b) =
        l.foldl (fun z x => z + u x) a +
          l.foldl (fun z x => z + v x) b := by
    induction l generalizing a b with
    | nil => rfl
    | cons x xs ih =>
        simpa [List.foldl, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]
          using ih (a + u x) (b + v x)
  simp only [otherSteps, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  have h := fold_add Arlib.Computation.Op.all
    (fun x => q.cost (CountingMatroid.Model.Operations.Op.word x))
    (fun x => (f q.val).cost (CountingMatroid.Model.Operations.Op.word x)) 0 0
  simp only [Nat.zero_add] at h
  rw [h]
  omega

/-- INTERNAL: Each multiplication in a charged natural power costs one word step. -/
private theorem natPower_otherSteps_eq (base exponent : ℕ) :
    otherSteps (CountingMatroid.Program.natPower base exponent) = exponent := by
  have hfold (l : List ℕ) (acc : ℕ) :
      otherSteps (Arlib.Computation.Charged.foldl
        (fun acc _ => CountingMatroid.Model.Operations.natMul acc base) l acc) =
        l.length := by
    induction l generalizing acc with
    | nil => simp [otherSteps]
    | cons x xs ih =>
        rw [show Arlib.Computation.Charged.foldl
          (fun acc _ => CountingMatroid.Model.Operations.natMul acc base)
          (x :: xs) acc =
          CountingMatroid.Model.Operations.natMul acc base >>= fun next =>
            Arlib.Computation.Charged.foldl
              (fun acc _ => CountingMatroid.Model.Operations.natMul acc base)
              xs next from rfl, otherSteps_bind]
        have hone : otherSteps (CountingMatroid.Model.Operations.natMul acc base) = 1 := by
          simp [otherSteps, CountingMatroid.Model.Operations.natMul,
            Arlib.Computation.CostVec.one, Arlib.Computation.Op.all]
        rw [hone, ih]
        simp only [List.length_cons]
        omega
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  simpa using hfold (List.range exponent) 1

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
  unfold CountingMatroid.Program.schedule
  simp only [otherSteps_bind, natPower_otherSteps_eq]
  -- BLOCKER: Directly expanding the charged schedule leaves a sum of costs
  -- for rational operands whose encoding sizes must be bounded. In particular
  -- the halving-loop rationals, η² and the observation quotient need bounds.
  sorry

end CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r11 · partial · proved charged sequencing and natural-power costs; isolated the
  halving-loop cost and imported its checked child statement. The full schedule
  cost still needs rational operand-size bounds and a sum of all primitive costs.
-/
