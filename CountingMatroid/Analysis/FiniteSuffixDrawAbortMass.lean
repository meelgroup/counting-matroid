import CountingMatroid.Analysis.BoundedUniformReplay
import CountingMatroid.Analysis.BoundedUniformAbortMass
import CountingMatroid.Analysis.FiniteTapePrefixBound

set_option autoImplicit false

/-!
Finite fair-suffix rejection bounds for the actual charged integer sampler.
The single-call bound uses the proved forced-leading-bit count for covered
rejection trials. The prefix-cylinder transfer below separates this stochastic
bound from the program's reachability and finite-block coverage proof.
-/

namespace CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: Any event on a fixed-length fair Boolean suffix has mass at
most one. This also handles a rejection cap of zero. -/
theorem suffix_event_mass_le_one (t : ℕ) (E : List Bool → Prop) :
    (Set.ncard {bits : List Bool | bits.length = t ∧ E bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 1 := by
  have hc : Set.ncard {bits : List Bool | bits.length = t ∧ E bits} ≤ 2 ^ t := by
    rw [← fair_lists_ncard t]
    exact Set.ncard_le_ncard (fun _ h => h.1) (List.finite_length_eq Bool t)
  calc
    _ ≤ ((2 ^ t : ℕ) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      exact mul_le_mul_left (Nat.cast_le.mpr hc) _
    _ = 1 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      have htwo : (2 : ENNReal) * (1 / 2) = 1 := by
        rw [div_eq_mul_inv, one_mul]
        exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
      rw [htwo, one_pow]

/-- INTERNAL: A covered positive-denominator call of the actual charged
sampler fails with fair-suffix mass at most two to the negative trial cap.
The prefix fixes the entire previous history; the starting cursor is exactly
its length, and the coverage premise includes every rejection trial.
TEXLINE: main.tex:1392-1421 -/
theorem bounded_uniform_suffix_abort_mass (pref : List Bool) (trials v t : ℕ)
    (hv : 0 < v) (hcoverage : trials * ((v - 1).log2 + 1) ≤ t) :
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
        trials v pref.length).val.1 = none} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ) := by
  classical
  by_cases hzero : trials = 0
  · subst trials
    simpa only [pow_zero, Rat.cast_one, ENNReal.ofReal_one] using
      suffix_event_mass_le_one t (fun suffix =>
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          0 v pref.length).val.1 = none)
  by_cases hone : v = 1
  · subst v
    simp [boundedUniform, Model.Operations.lessThan,
      Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_op,
      Arlib.Computation.Charged.val_pure]
  exact CountingMatroid.Analysis.FiniteObservationMarkov.ennreal_mass_of_rat_bound
    t _ ((1 / 2 : ℚ) ^ trials)
    (CountingMatroid.Analysis.BoundedUniformAbortMass.boundedUniform_abort_mass
      pref trials v t hv hcoverage)

/-- INTERNAL: A finite prefix-free family of reached draw histories, with
positive denominators and room for all capped trials in the remaining tape.
The histories are relative to a fixed external consumed prefix.
TEXLINE: main.tex:1392-1421 -/
structure DrawPrefixCover (trials t : ℕ) where
  prefixes : Finset (List Bool)
  denominator : List Bool → ℕ
  positive : ∀ head ∈ prefixes, 0 < denominator head
  covered : ∀ head ∈ prefixes,
    head.length + trials * ((denominator head - 1).log2 + 1) ≤ t
  prefix_free : ∀ a ∈ prefixes, ∀ b ∈ prefixes, a <+: b → a = b

/-- INTERNAL: Prefix-free reached calls with covered rejection trials have
the same abort bound even when their positive denominators depend on the
consumed history. The event retains the original defaulted finite tape.
TEXLINE: main.tex:1417-1421 -/
theorem adaptive_draw_abort_mass (pref : List Bool) (trials t : ℕ)
    (cover : DrawPrefixCover trials t) :
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      ∃ head ∈ cover.prefixes, head <+: suffix ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials (cover.denominator head) (pref.length + head.length)).val.1 = none} :
      ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ) := by
  classical
  let β := ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ)
  let part := fun head => {suffix : List Bool | suffix.length = t ∧
    head <+: suffix ∧
    (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
      trials (cover.denominator head) (pref.length + head.length)).val.1 = none}
  have hlen (head : List Bool) (hh : head ∈ cover.prefixes) : head.length ≤ t :=
    (Nat.le_add_right _ _).trans (cover.covered head hh)
  have hevent : {suffix : List Bool | suffix.length = t ∧
      ∃ head ∈ cover.prefixes, head <+: suffix ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials (cover.denominator head) (pref.length + head.length)).val.1 = none} =
      ⋃ head ∈ cover.prefixes, part head := by
    ext suffix
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, part]
    aesop
  have hpart (head : List Bool) (hh : head ∈ cover.prefixes) :
      (Set.ncard (part head) : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        (1 / 2 : ENNReal) ^ head.length * β := by
    rw [show (Set.ncard (part head) : ENNReal) * (1 / 2 : ENNReal) ^ t =
      (1 / 2 : ENNReal) ^ head.length *
        ((Set.ncard {tail : List Bool | tail.length = t - head.length ∧
          (boundedUniform (fun i => ((pref ++ (head ++ tail))[i]?).getD false)
            trials (cover.denominator head) (pref.length + head.length)).val.1 = none} :
            ENNReal) * (1 / 2 : ENNReal) ^ (t - head.length)) from
      append_event_mass t head (hlen head hh) (fun suffix =>
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials (cover.denominator head) (pref.length + head.length)).val.1 = none)]
    apply mul_le_mul_right _ _
    simpa only [List.append_assoc, List.length_append] using
      bounded_uniform_suffix_abort_mass (pref ++ head) trials
        (cover.denominator head) (t - head.length) (cover.positive head hh)
        (by have hc := cover.covered head hh; omega)
  rw [hevent]
  calc
    _ ≤ ((∑ head ∈ cover.prefixes, Set.ncard (part head) : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ t :=
      mul_le_mul_left (Nat.cast_le.mpr (cover.prefixes.set_ncard_biUnion_le part)) _
    _ = ∑ head ∈ cover.prefixes,
        (Set.ncard (part head) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ head ∈ cover.prefixes, (1 / 2 : ENNReal) ^ head.length * β :=
      Finset.sum_le_sum (fun head hh => hpart head hh)
    _ = (∑ head ∈ cover.prefixes, (1 / 2 : ENNReal) ^ head.length) * β :=
      (Finset.sum_mul ..).symm
    _ ≤ 1 * β := mul_le_mul_left
      (prefix_mass_le_one t cover.prefixes hlen cover.prefix_free) β
    _ = β := one_mul β

end CountingMatroid.Analysis.FiniteSuffixDrawAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r27 · proved · closed the covered single-call ENNReal abort bound using the existing rational rejection-cap theorem and finite-mass conversion; no new proof obligations.

* r26 · proved · prefix-cylinder summation transfers the single-call bound to adaptive positive denominators, retaining finite coverage explicitly.

* r26 · decomposed · separated covered rejection sampling from operational reachability; zero-trial and singleton-denominator cases proved, positive-trial counting and adaptive prefix transfer open.
-/
