import CountingMatroid.Model.Run

set_option autoImplicit false

namespace CountingMatroid.Analysis.LeastHalvingsCost

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: The exact encoding length of a halving accumulator.
TEXLINE: main.tex:1348-1351 -/
private theorem halfPower_binaryRatLength (i : ℕ) :
    binaryRatLength ((1 / 2 : ℚ) ^ i) = i + 4 := by
  have hn : (1 / 2 : ℚ).num = 1 := by norm_num
  have hd : (1 / 2 : ℚ).den = 2 := by norm_num
  unfold binaryRatLength binaryNatLength
  rw [Rat.num_pow, Rat.den_pow, hn, hd, Nat.log2_two_pow]
  norm_num
  have h : (1 : ℕ).log2 = 0 := by decide
  rw [h]
  omega

/-- INTERNAL: The capped halving search has polynomial charged work in its
input rational encoding and denominator cap. The loop's rational accumulator
is a power of one half, so its encoding grows by at most one bit per round.
TEXLINE: main.tex:1348-1351 -/
theorem leastHalvings_otherSteps_le (q : ℚ) :
    otherSteps (CountingMatroid.Program.leastHalvings q) ≤
      100 * (q.den.log2 + 8) *
        (binaryRatLength q + q.den.log2 + 16) ^ 2 + 1 := by
  -- The direct fold induction needs the invariant that the second accumulator
  -- component equals `(1 / 2 : ℚ) ^ b`, with `b` at most the elapsed rounds.
  -- `halfPower_binaryRatLength` closes the required encoding-size subgoal.
  -- The remaining induction must carry the accumulator identity across each
  -- successful `foldlWhile` step while summing its charged comparison/division.
  sorry

end CountingMatroid.Analysis.LeastHalvingsCost

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r11 · partial · proved the exact rational encoding length of a halving
  accumulator; the charged fold bound still needs the state invariant and sum.
-/
