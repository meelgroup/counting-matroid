import CountingMatroid.Model.Run

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace CountingMatroid.Analysis.ScheduleCostEnvelope

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Oracle charges add across charged sequencing. -/
theorem oracleCalls_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    oracleCalls (p >>= f) = oracleCalls p + oracleCalls (f p.val) := by
  simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]


/-- INTERNAL: A charged bounded search with no oracle operations in its body
has no oracle operations in its trace. -/
theorem oracleCalls_foldlWhile_zero {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (hf : ∀ b a, oracleCalls (f b a) = 0) (l : List α) (b : β) :
    oracleCalls (Arlib.Computation.Charged.foldlWhile f l b) = 0 := by
  induction l generalizing b with
  | nil => simp [oracleCalls]
  | cons a l ih =>
      cases h : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at h
          simp only [Arlib.Computation.Charged.foldlWhile, h]
          exact hf b a
      | some b' =>
          simp only [Arlib.Computation.Charged.val] at h
          simp only [Arlib.Computation.Charged.foldlWhile, h]
          have hb := hf b a
          have hl := ih b'
          simp only [oracleCalls] at hb hl ⊢
          simp only [Arlib.Computation.Charged.cost, Pi.add_apply] at hb hl ⊢
          omega

/-- INTERNAL: Iterating oracle-free arithmetic preserves zero oracle cost. -/
theorem oracleCalls_foldl_zero {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (hf : ∀ b a, oracleCalls (f b a) = 0) (l : List α) (b : β) :
    oracleCalls (Arlib.Computation.Charged.foldl f l b) = 0 := by
  induction l generalizing b with
  | nil => simp [oracleCalls]
  | cons a l ih =>
      simp only [Arlib.Computation.Charged.cost_foldl_cons, oracleCalls, Pi.add_apply]
      have hb := hf b a
      have hl := ih (f b a).val
      simp only [oracleCalls] at hb hl
      omega

/-- INTERNAL: A repeated natural multiplication never queries an oracle. -/
theorem natPower_oracleCalls_zero (base exponent : ℕ) :
    oracleCalls (CountingMatroid.Program.natPower base exponent) = 0 := by
  unfold CountingMatroid.Program.natPower Arlib.Computation.Charged.repeatFor
  apply oracleCalls_foldl_zero
  intro b a
  simp [oracleCalls, natMul, Arlib.Computation.CostVec.one]

/-- INTERNAL: The schedule's two bounded searches only execute word operations. -/
theorem leastHalvings_oracleCalls_zero (q : ℚ) :
    oracleCalls (CountingMatroid.Program.leastHalvings q) = 0 := by
  have hstep : ∀ b : ℕ × ℚ, ∀ a : ℕ,
      oracleCalls (do
        let needsStep ← ratLess q b.2
        if needsStep then
          let count ← successor b.1
          let power ← ratDiv b.2 2
          pure (some (count, power))
        else pure none) = 0 := by
    intro b a
    by_cases h : q < b.2 <;>
      simp [oracleCalls, ratLess, successor, ratDiv, h,
        Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many]
  have hfold := oracleCalls_foldlWhile_zero
    (fun b (_ : ℕ) => do
      let needsStep ← ratLess q b.2
      if needsStep then
        let count ← successor b.1
        let power ← ratDiv b.2 2
        pure (some (count, power))
      else pure none) hstep
    (List.range (q.den.log2 + 8)) (0, (1 : ℚ))
  unfold CountingMatroid.Program.leastHalvings
  simp only [oracleCalls_bind,
    Arlib.Computation.Charged.repeatWhile]
  simpa [oracleCalls, binaryLoopBound,
    Arlib.Computation.CostVec.one] using hfold

/-- INTERNAL: The drawing-width search only executes word operations. -/
theorem leastDrawTrials_oracleCalls_zero (M : ℕ) :
    oracleCalls (CountingMatroid.Program.leastDrawTrials M) = 0 := by
  have hstep : ∀ b : ℕ × ℕ, ∀ a : ℕ,
      oracleCalls (do
        let needsStep ← lessThan b.2 (32 * M)
        if needsStep then
          let count ← successor b.1
          let power ← natMul b.2 2
          pure (some (count, power))
        else pure none) = 0 := by
    intro b a
    by_cases h : b.2 < 32 * M <;>
      simp [oracleCalls, lessThan, successor, natMul, h,
        Arlib.Computation.CostVec.one]
  have hfold := oracleCalls_foldlWhile_zero
    (fun b (_ : ℕ) => do
      let needsStep ← lessThan b.2 (32 * M)
      if needsStep then
        let count ← successor b.1
        let power ← natMul b.2 2
        pure (some (count, power))
      else pure none) hstep
    (List.range (M.log2 + 8)) (1, 2)
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [oracleCalls_bind, Arlib.Computation.Charged.repeatWhile]
  simpa [oracleCalls, binaryLoopBound, natMul,
    Arlib.Computation.CostVec.one] using hfold

/-- INTERNAL: The charged construction of the schedule has polynomial cost
in the encoded input size. This is the cost part of the schedule resource envelope.
TEXLINE: main.tex:1348-1358 -/
theorem schedule_cost_envelope :
    ∃ (C degree : ℕ), ∀ (n r : ℕ) (p : InputParams),
      let inputSize := n + binaryInputLength n r p + Nat.ceil p.ε⁻¹ +
        binaryNatLength (Nat.ceil p.δ⁻¹) + 1
      let schedule := CountingMatroid.Program.schedule n p
      oracleCalls schedule ≤ C * inputSize ^ degree ∧
      otherSteps schedule ≤ C * inputSize ^ degree := by
  -- BLOCKER: The bounded-search and natural-power oracle charges are zero by
  -- the lemmas above. A straight-line schedule decomposition and polynomial
  -- encodings of eta and the observation quotient are still needed to sum
  -- the quadratic rational charges.
  sorry

end CountingMatroid.Analysis.ScheduleCostEnvelope

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r9 · open · zero oracle charges proved for bounded searches and natural powers; the full charged bound needs rational encoding estimates.
-/
