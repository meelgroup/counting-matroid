import CountingMatroid.Analysis.ObservableVarianceDecomposition

set_option autoImplicit false

/-!
The event selection and conditional-mean part of the paper's defect transfer
argument. The exchange transport estimate is separate: these results do not
assert an energy bound for transferring a defect mean to this event.
-/

namespace CountingMatroid.Analysis.TransversalEventMean

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open Arlib.Probability

/-- INTERNAL: The transversal event prescribing the x-element occupancy
at two specified original pairs. On a transversal this prescribes their
selected elements, with `false` selecting y and `true` selecting x.
TEXLINE: main.tex:868-873 -/
noncomputable def pairEvent {n : ℕ} (i k : Fin n) (a b : Bool) :
    Finset (PairedSet n) := by
  classical
  exact Finset.univ.filter (fun state =>
    (classifyState state).val = .transversal ∧
      decide ((i, false) ∈ state) = a ∧ decide ((k, false) ∈ state) = b)

/-- INTERNAL: Unnormalized probability mass of a finite event. -/
noncomputable def eventMass {n : ℕ} (π : FinDist (PairedSet n))
    (A : Finset (PairedSet n)) : ℝ := ∑ state ∈ A, π state

/-- INTERNAL: Conditional mean on a finite event, defined as zero when
the event has zero mass. -/
noncomputable def eventMean {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (A : Finset (PairedSet n)) : ℝ :=
  (∑ state ∈ A, π state * H state) / eventMass π A

/-- INTERNAL: The four prescribed two-pair events partition the transversal
mass. This also holds when the two indices coincide; two cells are then empty.
TEXLINE: main.tex:868-873 -/
theorem pair_event_mass_partition {n : ℕ} (π : FinDist (PairedSet n))
    (i k : Fin n) :
    (∑ a : Bool, ∑ b : Bool, eventMass π (pairEvent i k a b)) =
      classMass π .transversal := by
  classical
  simp only [eventMass, pairEvent, Finset.sum_filter, classMass]
  rw [Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun _ _ => Finset.sum_comm)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro state _
  by_cases hT : (classifyState state).val = .transversal
  · by_cases hi : (i, false) ∈ state <;> by_cases hk : (k, false) ∈ state <;>
      simp [hT, hi, hk]
  · simp [hT]

/-- PAPER: main.tex:868-873
One of the four assignments at the specified pairs carries at least
one quarter of the transversal mass. -/
theorem large_pair_event {n : ℕ} (π : FinDist (PairedSet n)) (i k : Fin n) :
    ∃ a b : Bool,
      classMass π .transversal / 4 ≤ eventMass π (pairEvent i k a b) := by
  have hpart := pair_event_mass_partition π i k
  rw [Fintype.sum_bool, Fintype.sum_bool, Fintype.sum_bool] at hpart
  by_contra h
  push_neg at h
  have hff := h false false
  have hft := h false true
  have htf := h true false
  have htt := h true true
  linarith

/-- INTERNAL: Weighted Cauchy--Schwarz bounds a finite event's centered
mean without any full-support requirement on its individual states.
TEXLINE: main.tex:909-911 -/
theorem event_centered_sum_sq_le {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (A : Finset (PairedSet n)) (c : ℝ) :
    (∑ state ∈ A, π state * (H state - c)) ^ 2 ≤
      eventMass π A * (∑ state ∈ A, π state * (H state - c) ^ 2) := by
  apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (f := fun state => π state) (g := fun state => π state * (H state - c) ^ 2)
    A (fun state _ => π.coe_nonneg state)
    (fun state _ => mul_nonneg (π.coe_nonneg state) (sq_nonneg _))
  intro state _
  exact le_of_eq (by ring)

/-- PAPER: main.tex:909-911
The conditional mean of a two-pair transversal event of probability at least
one quarter differs from the full transversal mean by at most four times
the transversal variance in squared deviation. -/
theorem large_pair_event_mean_bound {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (i k : Fin n) (a b : Bool)
    (hp : 0 < classMass π .transversal)
    (hlarge : classMass π .transversal / 4 ≤ eventMass π (pairEvent i k a b)) :
    (eventMean π H (pairEvent i k a b) - classMean π H .transversal) ^ 2 ≤
      4 * transversalVariance π H := by
  classical
  let A := pairEvent i k a b
  let p := classMass π .transversal
  let m := classMean π H .transversal
  let s := eventMass π A
  let T := ∑ state : PairedSet n,
    if (classifyState state).val = .transversal then π state * (H state - m) ^ 2 else 0
  have hs : 0 < s := (div_pos hp (by norm_num)).trans_le hlarge
  have hsum : (∑ state ∈ A, π state * (H state - m)) =
      s * (eventMean π H A - m) := by
    simp only [eventMean, mul_sub, Finset.sum_sub_distrib]
    change (∑ state ∈ A, π state * H state) - (∑ state ∈ A, π state * m) = _
    rw [← Finset.sum_mul]
    change _ = s * ((∑ state ∈ A, π state * H state) / s) - s * m
    rw [mul_div_cancel₀ _ hs.ne']
    rfl
  have hmoment : (∑ state ∈ A, π state * (H state - m) ^ 2) ≤ T := by
    dsimp only [A, pairEvent, T]
    rw [Finset.sum_filter]
    apply Finset.sum_le_sum
    intro state _
    by_cases hT : (classifyState state).val = .transversal
    · simp only [hT, true_and, if_true]
      split_ifs
      · exact le_rfl
      · exact mul_nonneg (π.coe_nonneg state) (sq_nonneg _)
    · simp only [hT, false_and, if_false, le_refl]
  have hcs := event_centered_sum_sq_le π H A m
  rw [hsum] at hcs
  have hbound : s * (eventMean π H A - m) ^ 2 ≤ T := by
    have hmul := mul_le_mul_of_nonneg_left hmoment hs.le
    nlinarith [hcs]
  have hl : p ≤ 4 * s := by dsimp only [p, s, A]; linarith [hlarge]
  have hscaled : p * (eventMean π H A - m) ^ 2 ≤ 4 * T := by
    have hmul := mul_le_mul_of_nonneg_right hl
      (sq_nonneg (eventMean π H A - m))
    linarith
  change (eventMean π H A - m) ^ 2 ≤ 4 * (T / p)
  rw [← mul_div_assoc]
  exact (le_div_iff₀ hp).mpr (by nlinarith [hscaled])

end CountingMatroid.Analysis.TransversalEventMean
