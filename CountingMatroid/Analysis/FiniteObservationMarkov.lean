import CountingMatroid.Analysis.FiniteTapePrefixBound
import CountingMatroid.Analysis.RelativeObservationBounds

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteObservationMarkov

open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: A failed relative estimate whose mean is bounded below has
squared deviation at least the square of the corresponding absolute threshold.
TEXLINE: main.tex:1253-1266 -/
theorem relative_failure_square (η a mean estimate : ℚ)
    (hη : 0 < η) (ha : 0 < a) (hm : a ≤ mean)
    (hbad : ¬ RelativeEstimate η mean estimate) :
    (η * a) ^ 2 ≤ (estimate - mean) ^ 2 := by
  have hthreshold : 0 < η * a := mul_pos hη ha
  have hcompare : η * a ≤ η * mean := mul_le_mul_of_nonneg_left hm hη.le
  rcases not_and_or.mp hbad with hl | hu
  · have hleft : estimate < (1 - η) * mean := lt_of_not_ge hl
    have hdelta : estimate - mean < -(η * a) := by nlinarith
    nlinarith [sq_nonneg (estimate - mean + η * a)]
  · have hright : (1 + η) * mean < estimate := lt_of_not_ge hu
    have hdelta : η * a < estimate - mean := by nlinarith
    nlinarith [sq_nonneg (estimate - mean - η * a)]

/-- INTERNAL: Discrete Markov inequality with no independence hypothesis.
The error can be a masked squared deviation on successful executions.
TEXLINE: main.tex:1253-1266 -/
theorem finite_markov_card {α : Type} [Fintype α] (bad : α → Prop)
    (error : α → ℚ) (threshold : ℚ)
    (herror : ∀ x, 0 ≤ error x) (hbad : ∀ x, bad x → threshold ≤ error x) :
    letI := Classical.propDecidable
    ((Finset.univ.filter bad).card : ℚ) * threshold ≤ ∑ x, error x := by
  classical
  calc
    ((Finset.univ.filter bad).card : ℚ) * threshold =
        ∑ _x ∈ Finset.univ.filter bad, threshold := by simp
    _ ≤ ∑ x ∈ Finset.univ.filter bad, error x := by
      apply Finset.sum_le_sum
      intro x hx
      exact hbad x (Finset.mem_filter.mp hx).2
    _ ≤ ∑ x, error x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun x _ _ => herror x)

/-- INTERNAL: Uniform length-t tape events have the same cardinality when
represented by fixed-length vectors, enabling finite-sum moment arguments.
TEXLINE: main.tex:1392-1421 -/
theorem event_card_vectors (t : ℕ) (bad : List Bool → Prop) :
    letI := Classical.propDecidable
    Set.ncard {bits : List Bool | bits.length = t ∧ bad bits} =
      (Finset.univ.filter (fun bits : List.Vector Bool t => bad bits.val)).card := by
  classical
  let S := {bits : List Bool // bits.length = t ∧ bad bits}
  let T := {bits : List.Vector Bool t // bad bits.val}
  let join : T → S := fun bits => ⟨bits.val.val, bits.val.property, bits.property⟩
  have hj : Function.Bijective join := by
    constructor
    · intro a b he
      apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun x : S => x.val) he
    · intro bits
      exact ⟨⟨⟨bits.val, bits.property.1⟩, bits.property.2⟩, rfl⟩
  have hcard := Nat.card_congr (Equiv.ofBijective join hj)
  change Nat.card S = _
  rw [← hcard]
  change Nat.card {bits : List.Vector Bool t // bad bits.val} = _
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]

/-- INTERNAL: Convert a rational finite-tape mass estimate to ENNReal,
matching the cardinality normalization used by the lower-tail theorem.
TEXLINE: main.tex:1392-1427 -/
theorem ennreal_mass_of_rat_bound (t card : ℕ) (bound : ℚ)
    (h : (card : ℚ) / (2 : ℚ) ^ t ≤ bound) :
    (card : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ ENNReal.ofReal bound := by
  have hr := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at hr
  have he := ENNReal.ofReal_le_ofReal hr
  rw [ENNReal.ofReal_div_of_pos (by positivity : (0 : ℝ) < 2 ^ t),
    ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 2), ENNReal.ofReal_natCast,
    ENNReal.ofReal_ofNat] at he
  simpa only [div_pow, one_pow, div_eq_mul_inv, one_mul, ENNReal.inv_pow] using he

/-- INTERNAL: Markov and the finite observable union bound, expressed using
masked second moments rather than an independence claim about observations.
TEXLINE: main.tex:1253-1266 -/
theorem finite_family_markov {α β : Type} [Fintype α] [Fintype β]
    (bad : α → Prop) (error : α → β → ℚ) (weight threshold bound : ℚ)
    (hweight : 0 ≤ weight) (hthreshold : 0 < threshold)
    (herror : ∀ x i, 0 ≤ error x i)
    (hbad : ∀ x, bad x → ∃ i, threshold ≤ error x i)
    (hmoment : ∀ i, (∑ x, error x i) * weight ≤ bound) :
    letI := Classical.propDecidable
    ((Finset.univ.filter bad).card : ℚ) * weight ≤
      (Fintype.card β : ℚ) * bound / threshold := by
  classical
  have hmarkov := finite_markov_card bad (fun x => ∑ i, error x i) threshold
    (fun x => Finset.sum_nonneg (fun i _ => herror x i)) (by
      intro x hx
      obtain ⟨i, hi⟩ := hbad x hx
      exact hi.trans (Finset.single_le_sum (fun k _ => herror x k) (Finset.mem_univ i)))
  have htotal : (∑ x, ∑ i, error x i) * weight ≤ (Fintype.card β : ℚ) * bound := by
    rw [Finset.sum_comm, Finset.sum_mul]
    simpa only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul] using
      Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hmoment i)
  apply (le_div_iff₀ hthreshold).mpr
  have hweighted := mul_le_mul_of_nonneg_right hmarkov hweight
  nlinarith

end CountingMatroid.Analysis.FiniteObservationMarkov
