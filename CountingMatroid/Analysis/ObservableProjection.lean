import CountingMatroid.Analysis.IdealExchangeChain
import CountingMatroid.Analysis.TypeMassLowerBounds
import Arlib.MarkovChains.Techniques.Dirichlet

set_option autoImplicit false

namespace CountingMatroid.Analysis.ObservableProjection

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Extend the paper's observable projection to all paired subsets:
retain transversal values, replace each defect class by its conditional mean,
and set rejected states to zero. The operational law gives rejected states
zero mass, so their extension does not affect variance or energy.
TEXLINE: main.tex:913-921 -/
noncomputable def observableProjection {n : ℕ} (π : FinDist (PairedSet n))
    (H : PairedSet n → ℝ) (state : PairedSet n) : ℝ :=
  match (classifyState state).val with
  | .transversal => H state
  | .defect i k =>
      (∑ next : PairedSet n,
        if (classifyState next).val = .defect i k then π next * H next else 0) /
      (∑ next : PairedSet n,
        if (classifyState next).val = .defect i k then π next else 0)
  | .invalid => 0

/-- INTERNAL: The operational type indicator is fixed by the observable
projection on every state of positive target mass, expressed without a
full-support assumption. This is the range condition needed for the MSE bound.
TEXLINE: main.tex:1238-1240 -/
theorem type_indicator_projected {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (kind : StateKind n) (state : PairedSet n) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    π state * observableProjection π (typeIndicator kind) state =
      π state * typeIndicator kind state := by
  classical
  intro π
  by_cases hzero : π state = 0
  · simp [hzero]
  cases hk : (classifyState state).val with
  | invalid =>
    have hm : π state = 0 := by
      simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk, weightOfKind]
    simp [hm]
  | transversal => simp [observableProjection, hk]
  | defect i k =>
    let mass := ∑ next : PairedSet n,
      if (classifyState next).val = .defect i k then π next else 0
    have hnonneg (next : PairedSet n) :
        0 ≤ if (classifyState next).val = .defect i k then π next else 0 := by
      split_ifs
      · exact π.coe_nonneg next
      · exact le_rfl
    have hmass : 0 < mass := by
      have hsingle := Finset.single_le_sum
        (fun next _ => hnonneg next) (Finset.mem_univ state)
      simp only [hk, if_pos rfl] at hsingle
      exact (lt_of_le_of_ne (π.coe_nonneg state) (Ne.symm hzero)).trans_le hsingle
    have hnum : (∑ next : PairedSet n,
        if (classifyState next).val = .defect i k then
          π next * typeIndicator kind next else 0) =
        if StateKind.defect i k = kind then mass else 0 := by
      by_cases ht : StateKind.defect i k = kind
      · rw [if_pos ht]
        apply Finset.sum_congr rfl
        intro next _
        by_cases hn : (classifyState next).val = .defect i k
        · simp [hn, typeIndicator, ht]
        · simp [hn]
      · rw [if_neg ht]
        apply Finset.sum_eq_zero
        intro next _
        by_cases hn : (classifyState next).val = .defect i k
        · simp [hn, typeIndicator, ht]
        · simp [hn]
    simp only [observableProjection, hk]
    change π state * ((∑ next : PairedSet n,
      if (classifyState next).val = .defect i k then
        π next * typeIndicator kind next else 0) / mass) = _
    rw [hnum]
    by_cases ht : StateKind.defect i k = kind <;>
      simp [ht, hmass.ne', typeIndicator, hk]

/-- INTERNAL: The annealing observable is fixed pointwise by the observable
projection: its defect-class averages are zero and its transversal values
are retained. This is the second range condition used by the MSE argument.
TEXLINE: main.tex:1238-1240 -/
theorem numerator_observable_projected {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (ρ : ℚ) (π : FinDist (PairedSet n)) :
    observableProjection π (numeratorObservable r o₁ o₂ ρ) =
      numeratorObservable r o₁ o₂ ρ := by
  classical
  funext state
  cases hk : (classifyState state).val with
  | invalid => simp [observableProjection, numeratorObservable, hk]
  | transversal => simp [observableProjection, numeratorObservable, hk]
  | defect i k =>
    have hnum : (∑ next : PairedSet n,
        if (classifyState next).val = .defect i k then
          π next * numeratorObservable r o₁ o₂ ρ next else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro next _
      by_cases hn : (classifyState next).val = .defect i k
      · simp [numeratorObservable, hn]
      · simp [hn]
    simp only [observableProjection, hk, hnum, zero_div]
    simp [numeratorObservable, hk]

end CountingMatroid.Analysis.ObservableProjection
