import CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

set_option autoImplicit false

namespace CountingMatroid.Analysis.RationalHeight
open CountingMatroid.Model

/-- INTERNAL: The larger component length supports additive growth under rational addition.
TEXLINE: main.tex:1362-1378 -/
def rationalHeight (q : ℚ) : ℕ :=
  max q.num.natAbs.log2 q.den.log2 + 1

/-- INTERNAL: Component height is bounded by the full encoding length. -/
theorem rationalHeight_le_length (q : ℚ) : rationalHeight q ≤ binaryRatLength q := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega

/-- INTERNAL: Two component lengths bound the rational encoding length. -/
theorem binaryRatLength_le_height (q : ℚ) :
    binaryRatLength q ≤ 2 * rationalHeight q + 2 := by
  unfold rationalHeight binaryRatLength binaryNatLength
  omega

/-- INTERNAL: Each rational component fits in the power of two specified by its height. -/
private theorem components_lt (q : ℚ) :
    q.num.natAbs < 2 ^ rationalHeight q ∧ q.den < 2 ^ rationalHeight q := by
  have bound (a b : ℕ) (h : a.log2 ≤ b) : a < 2 ^ (b + 1) := by
    have ha := Nat.lt_pow_succ_log_self Nat.one_lt_two a
    rw [← Nat.log2_eq_log_two] at ha
    exact ha.trans_le (Nat.pow_le_pow_right (by decide) (by omega))
  exact ⟨bound _ _ (le_max_left _ _), bound _ _ (le_max_right _ _)⟩

/-- INTERNAL: Rational addition increases component height by at most the sum
of the operand heights and one carry bit. TEXLINE: main.tex:1362-1378 -/
theorem rationalHeight_add_le (a b : ℚ) :
    rationalHeight (a + b) ≤ rationalHeight a + rationalHeight b + 1 := by
  have hd : (a + b).den ≤ a.den * b.den :=
    Nat.le_of_dvd (Nat.mul_pos a.den_pos b.den_pos) (Rat.add_den_dvd a b)
  have heq := congrArg Int.natAbs (Rat.add_num_den' a b)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at heq
  have hn := Int.natAbs_add_le (a.num * b.den) (b.num * a.den)
  simp only [Int.natAbs_mul, Int.natAbs_natCast] at hn
  have hnum : (a + b).num.natAbs ≤ a.num.natAbs * b.den + b.num.natAbs * a.den := by
    have hdenpos := Nat.mul_pos a.den_pos b.den_pos
    have hmul := Nat.mul_le_mul hn hd
    nlinarith
  obtain ⟨han, had⟩ := components_lt a
  obtain ⟨hbn, hbd⟩ := components_lt b
  have hp : 0 < 2 ^ (rationalHeight a + rationalHeight b) := by positivity
  have hprod₁ : a.num.natAbs * b.den < 2 ^ (rationalHeight a + rationalHeight b) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le han hbd.le (by positivity)
  have hprod₂ : b.num.natAbs * a.den < 2 ^ (rationalHeight a + rationalHeight b) := by
    rw [add_comm, pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le hbn had.le (by positivity)
  have hdprod : a.den * b.den < 2 ^ (rationalHeight a + rationalHeight b) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_le had hbd.le (by positivity)
  have hnlt : (a + b).num.natAbs < 2 ^ (rationalHeight a + rationalHeight b + 1) := by
    rw [pow_succ]
    omega
  have hdlt : (a + b).den < 2 ^ (rationalHeight a + rationalHeight b + 1) := by
    rw [pow_succ]
    omega
  have logbound (m : ℕ) (hm : m < 2 ^ (rationalHeight a + rationalHeight b + 1)) :
      m.log2 < rationalHeight a + rationalHeight b + 1 := by
    by_cases hz : m = 0
    · subst m; simp
    · rw [Nat.log2_eq_log_two]
      exact (Nat.log_lt_iff_lt_pow (by decide) hz).2 hm
  have hnlog := logbound _ hnlt
  have hdlog := logbound _ hdlt
  change max (a + b).num.natAbs.log2 (a + b).den.log2 + 1 ≤ _
  omega
end CountingMatroid.Analysis.RationalHeight
