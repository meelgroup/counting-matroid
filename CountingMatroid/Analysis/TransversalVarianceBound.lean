import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.OnePairObservablePoincare

set_option autoImplicit false

/-!
The paper's transversal variance estimate, isolated from the final observable
variance bookkeeping. The one-pair case is proved using the existing
constant-two Poincare estimate. For at least two pairs the remaining proof
is the adaptive binary conditioning tree, including coefficient-score sink
selection, transport at each split, and the per-depth disjoint-edge charge.
-/

namespace CountingMatroid.Analysis.TransversalVarianceBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist

/-- INTERNAL: If a probability law is supported on transversals, its
transversal conditional variance is its ordinary variance, and the
observable projection agrees with the observable almost everywhere.
TEXLINE: main.tex:832-839 -/
theorem transversal_variance_eq_of_supported {n : ℕ}
    (π : FinDist (PairedSet n)) (H : PairedSet n → ℝ)
    (hsupport : ∀ state, (classifyState state).val ≠ .transversal → π state = 0) :
    classMass π .transversal = 1 ∧
      transversalVariance π H = Var π (observableProjection π H) := by
  classical
  have hm : classMass π .transversal = 1 := by
    calc
      classMass π .transversal = ∑ state, π state := by
        apply Finset.sum_congr rfl
        intro state _
        by_cases ht : (classifyState state).val = .transversal
        · simp only [if_pos ht]
        · simp only [if_neg ht, hsupport state ht]
      _ = 1 := π.sum_coe
  have hmean : classMean π H .transversal = Ex π H := by
    unfold classMean
    rw [hm, div_one]
    apply Finset.sum_congr rfl
    intro state _
    by_cases ht : (classifyState state).val = .transversal
    · simp only [if_pos ht]
    · simp only [if_neg ht, hsupport state ht, zero_mul]
  refine ⟨hm, ?_⟩
  have hv : transversalVariance π H = Var π H := by
    unfold transversalVariance
    rw [hm, div_one, hmean, Var_apply]
    apply Finset.sum_congr rfl
    intro state _
    by_cases ht : (classifyState state).val = .transversal
    · simp only [if_pos ht]
    · simp only [if_neg ht, hsupport state ht, zero_mul]
  rw [hv]
  apply Var_congr_ae
  intro state hpos
  have ht : (classifyState state).val = .transversal := by
    by_contra h
    exact hpos (hsupport state h)
  simp only [observableProjection, ht]

/-- PAPER: main.tex:777-839
The transversal conditional variance is bounded by the paper's constant
`n(1+8n)` times `D(H)/c₀`, expressed with normalized ideal conductances. -/
theorem transversal_variance_bound (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index))
    (H : PairedSet n → ℝ) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    transversalVariance π H ≤ (n : ℝ) * (1 + 8 * (n : ℝ)) *
      (2 * (n : ℝ) ^ 2 * potentialEnergy κ H / classMass π .transversal) := by
  classical
  intro π κ
  by_cases hn1 : n = 1
  · subst n
    have hsupport : ∀ state, (classifyState state).val ≠ .transversal →
        π state = 0 := by
      intro state ht
      cases hk : (classifyState state).val with
      | transversal => exact False.elim (ht hk)
      | invalid =>
          simp [π, operationalLaw, StationaryMeanIdentities.stateWeight,
            hk, weightOfKind]
      | defect i k =>
          have hik : i = k := Subsingleton.elim _ _
          simp [π, operationalLaw, StationaryMeanIdentities.stateWeight,
            hk, weightOfKind, hik]
    obtain ⟨hmass, hvariance⟩ := transversal_variance_eq_of_supported π H hsupport
    have hzero : π ∅ = 0 := hsupport ∅ (by decide)
    have hfullstate : π {(0, false), (0, true)} = 0 :=
      hsupport _ (by decide)
    have hbase : Var π (observableProjection π H) ≤ 2 * potentialEnergy κ H :=
      OnePairObservablePoincare.one_pair_observable_poincare π hzero hfullstate H
    have henergy : 0 ≤ potentialEnergy κ H := by
      apply potential_energy_nonneg
      intro state next
      exact mul_nonneg ((exchangeProposal 1 hn).coe_nonneg state next)
        (le_min (π.coe_nonneg state) (π.coe_nonneg next))
    rw [hvariance, hmass]
    norm_num
    nlinarith [hbase]
  have htwo : 2 ≤ n := by omega
  have hp : 1 / (5 * (n : ℝ) ^ 2) ≤ classMass π .transversal := by
    dsimp only [π]
    rw [operational_class_mass]
    have hmass := (TypeMassLowerBounds.good_type_mass_bounds
      r o₁ o₂ q w hn hq hgood).2.1
    have hcast := (Rat.cast_le (K := ℝ)).mpr hmass
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hcast
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hp₀ : 0 < classMass π .transversal :=
    (div_pos (by norm_num) (by positivity)).trans_le hp
  rw [← mul_div_assoc]
  apply (le_div_iff₀ hp₀).mpr
  rw [transversalVariance, div_mul_cancel₀ _ hp₀.ne']
  -- Concrete route: clear the positive class mass to reach exactly the
  -- unnormalized variance charged by the tree in main.tex:832-839.
  -- STILL OPEN (missing local lemmas, htwo : 2 ≤ n): neither the project
  -- nor the pinned libraries expose the conditional coefficient bounds
  -- of main.tex:397-449 or the slot transport bound of main.tex:455-709.
  -- For a partial assignment σ, the first required bounds are
  --   4*c^σ_ij*c^σ_ji ≤ zσ^2 and c^σ_ij*c^σ_jk ≤ zσ*c^σ_ik,
  -- with distinct unassigned indices. They must be proved for the actual
  -- q^(n-pairedRank) weights using hfull, hr, h₁, h₂, hq and hqone.
  -- The second required bound is
  --   (mean_p H - mean_d H)^2 ≤
  --     (1/(s_p*W_p) + 1/(s_d*W_d) +
  --       2/(s_p*s_d)*sum_t(v_t/W_t)) * D_slots(H),
  -- for the singleton/ordinary-slot classes in main.tex:465-492.
  -- ExchangeFlowEnergy.flow_energy_bound supplies its Cauchy--Schwarz
  -- implication only after an exchange-supported balanced flow and its
  -- energy bound have been constructed; no such slot flow is exposed.
  -- Once these are proved, construct the score-sink conditioning tree,
  -- telescope binary variance, and charge disjoint edges at each depth.
  -- Var_push_eq in Arlib.MarkovChains.Techniques.LevelVariance is an
  -- available variance identity, but it does not construct this tree or
  -- establish its node transport bounds. Direct entrywise comparison
  -- fails on non-neighboring transversals of zero exchange conductance.
  sorry

end CountingMatroid.Analysis.TransversalVarianceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · partial · proved the supported-law variance bridge and the n=1 branch; exposed the n≥2 centered moment after positive-mass cancellation. Conditional coefficient bounds (397-449) and slot transport (455-709) are missing local lemmas; no new open helper was introduced.
-/
