import CountingMatroid.Analysis.ObservableProjection

set_option autoImplicit false

/-!
Weighted moments for the operational classifier, and the first inequality
in the paper's observable Poincare proof. These identities do not assert
the quantitative transversal variance or defect transport estimates.
-/

namespace CountingMatroid.Analysis.ObservableVarianceDecomposition

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist

/-- INTERNAL: Mass of a classifier fiber, including zero-mass fibers.
TEXLINE: main.tex:913-951 -/
noncomputable def classMass {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) : ℝ := by
  classical
  exact ∑ state : PairedSet n,
    if (classifyState state).val = kind then π state else 0

/-- INTERNAL: Conditional mean on a classifier fiber; the quotient is zero
when that fiber has zero mass.
TEXLINE: main.tex:858-921 -/
noncomputable def classMean {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (kind : StateKind n) : ℝ := by
  classical
  exact (∑ state : PairedSet n,
    if (classifyState state).val = kind then π state * H state else 0) /
      classMass π kind

/-- INTERNAL: Conditional transversal variance, written as a weighted
moment so that no separate full-support distribution is required.
TEXLINE: main.tex:784-857 -/
noncomputable def transversalVariance {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) : ℝ := by
  classical
  exact (∑ state : PairedSet n,
    if (classifyState state).val = .transversal then
      π state * (H state - classMean π H .transversal) ^ 2 else 0) /
        classMass π .transversal

/-- INTERNAL: A classifier fiber has nonnegative probability mass. -/
theorem class_mass_nonneg {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) : 0 ≤ classMass π kind := by
  classical
  apply Finset.sum_nonneg
  intro state _
  split_ifs
  · exact π.coe_nonneg state
  · exact le_rfl

/-- INTERNAL: Restricting a probability sum to one classifier fiber cannot
increase its mass. -/
theorem class_mass_le_one {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) : classMass π kind ≤ 1 := by
  classical
  unfold classMass
  calc
    (∑ state : PairedSet n,
        if (classifyState state).val = kind then π state else 0) ≤
        ∑ state : PairedSet n, π state := by
      apply Finset.sum_le_sum
      intro state _
      split_ifs
      · exact le_rfl
      · exact π.coe_nonneg state
    _ = 1 := π.sum_coe

/-- INTERNAL: The conditional transversal second moment is nonnegative. -/
theorem transversal_variance_nonneg {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) : 0 ≤ transversalVariance π H := by
  classical
  unfold transversalVariance
  apply div_nonneg _ (class_mass_nonneg π .transversal)
  apply Finset.sum_nonneg
  intro state _
  split_ifs
  · exact mul_nonneg (π.coe_nonneg state) (sq_nonneg _)
  · exact le_rfl

/-- INTERNAL: The classifier-fiber mass equals the operational type mean.
TEXLINE: main.tex:721-744 -/
theorem operational_class_mass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) (kind : StateKind n) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) kind =
      (StationaryMeanIdentities.typeMean r o₁ o₂ q w kind : ℝ) := by
  classical
  rw [← operational_type_mean r o₁ o₂ q w hq hw kind]
  simp [classMass, Ex, typeIndicator]

/-- INTERNAL: The transversal, defect and rejected classifier labels
partition the probability space. -/
theorem class_mass_partition {n : ℕ} (π : FinDist (PairedSet n)) :
    classMass π .transversal +
      (∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k)) +
      classMass π .invalid = 1 := by
  classical
  have hcell (state : PairedSet n) :
      (if (classifyState state).val = .transversal then π state else 0) +
        (∑ i : Fin n, ∑ k : Fin n,
          if (classifyState state).val = .defect i k then π state else 0) +
        (if (classifyState state).val = .invalid then π state else 0) =
        π state := by
    cases (classifyState state).val <;> simp [ite_and]
  have hdef : (∑ i : Fin n, ∑ k : Fin n, classMass π (.defect i k)) =
      ∑ state : PairedSet n, ∑ i : Fin n, ∑ k : Fin n,
        if (classifyState state).val = .defect i k then π state else 0 := by
    unfold classMass
    calc
      (∑ i : Fin n, ∑ k : Fin n, ∑ state : PairedSet n,
          if (classifyState state).val = .defect i k then π state else 0) =
          ∑ i : Fin n, ∑ state : PairedSet n, ∑ k : Fin n,
            if (classifyState state).val = .defect i k then π state else 0 :=
        Finset.sum_congr rfl (fun i _ => Finset.sum_comm)
      _ = _ := Finset.sum_comm
  rw [hdef]
  unfold classMass
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  rw [Finset.sum_congr rfl (fun state _ => hcell state)]
  exact π.sum_coe

/-- INTERNAL: Rejected classifier states have zero operational mass. -/
theorem operational_invalid_mass_zero {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) .invalid = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro state _
  by_cases hk : (classifyState state).val = .invalid
  · simp [hk, operationalLaw, StationaryMeanIdentities.stateWeight, weightOfKind]
  · simp [hk]

/-- INTERNAL: Diagonal defect labels have zero operational mass, even
without a separate correctness theorem for the classifier. -/
theorem diagonal_class_mass_zero {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index) (i : Fin n) :
    classMass (operationalLaw r o₁ o₂ q w hq hw) (.defect i i) = 0 := by
  classical
  apply Finset.sum_eq_zero
  intro state _
  by_cases hk : (classifyState state).val = .defect i i
  · simp [hk, operationalLaw, StationaryMeanIdentities.stateWeight, weightOfKind]
  · simp [hk]

/-- PAPER: main.tex:938-942
Variance is bounded by deviation from the transversal mean. The projected
defect values contribute only the squared deviations of their class means.
The sum includes diagonal classifier labels, whose operational mass is zero.
-/
theorem observable_variance_decomposition {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (H : PairedSet n → ℝ) (c : ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    Var π (observableProjection π H) ≤
      (∑ state : PairedSet n,
        if (classifyState state).val = .transversal then
          π state * (H state - c) ^ 2 else 0) +
      ∑ i : Fin n, ∑ k : Fin n,
        classMass π (.defect i k) * (classMean π H (.defect i k) - c) ^ 2 := by
  classical
  intro π
  have hbound := Var_le_ip_self π (fun state => observableProjection π H state - c)
  rw [Var_sub_const] at hbound
  refine hbound.trans_eq ?_
  unfold ip
  have hcell (state : PairedSet n) :
      π state * (observableProjection π H state - c) *
          (observableProjection π H state - c) =
        (if (classifyState state).val = .transversal then
          π state * (H state - c) ^ 2 else 0) +
        ∑ i : Fin n, ∑ k : Fin n,
          if (classifyState state).val = .defect i k then
            π state * (classMean π H (.defect i k) - c) ^ 2 else 0 := by
    cases hk : (classifyState state).val with
    | invalid =>
      have hm : π state = 0 := by
        simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk,
          weightOfKind]
      simp [hm]
    | transversal => simp [hk, observableProjection, pow_two, mul_assoc]
    | defect i k =>
      simp [hk, observableProjection, classMean, classMass, pow_two,
        ite_and, mul_assoc]
  rw [Finset.sum_congr rfl (fun state _ => hcell state), Finset.sum_add_distrib]
  congr 1
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  unfold classMass
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro state _
  split_ifs <;> simp

end CountingMatroid.Analysis.ObservableVarianceDecomposition

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* current · proved · classifier mass identities, nonnegative transversal variance, and the projection's squared-deviation decomposition, including rejected and diagonal zero-mass classes.
-/
