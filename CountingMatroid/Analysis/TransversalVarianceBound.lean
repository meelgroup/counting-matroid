import CountingMatroid.Analysis.ExchangeFlowEnergy

set_option autoImplicit false

/-!
The paper's transversal variance estimate, isolated from the final observable
variance bookkeeping. Its remaining proof is the adaptive binary conditioning
tree, including coefficient-score sink selection, transport at each split,
and the per-depth disjoint-edge charge.
-/

namespace CountingMatroid.Analysis.TransversalVarianceBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.ExchangeFlowEnergy

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
  -- Concrete route: clear the positive class mass to reach exactly the
  -- unnormalized variance charged by the tree in main.tex:832-839.
  -- STILL OPEN: construct the adaptive conditioning tree using the
  -- conditional defect inequalities (397-449) to choose a score sink;
  -- prove its binary variance decomposition and its per-depth edge
  -- disjointness, then apply slot transport to each branching node.
  -- Var_push_eq in Arlib.MarkovChains.Techniques.LevelVariance is an
  -- available variance identity, but it does not construct this tree or
  -- establish its node transport bounds. Direct entrywise comparison
  -- fails on non-neighboring transversals of zero exchange conductance.
  sorry

end CountingMatroid.Analysis.TransversalVarianceBound
