import CountingMatroid.Analysis.ExchangeFlowEnergy

set_option autoImplicit false

/-!
The signed exchange current needed for the paper's defect-mean transport.
Its required source and sink are the actual conditional densities, and its
cost uses the normalized ideal-exchange conductances. The dense product
current below has the right divergence but cannot satisfy exchange support;
the remaining construction must use the paper's recursive leaf cliques.
-/

namespace CountingMatroid.Analysis.DefectMeanExchangeFlow

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: A normalized exchange-supported current from an ordered defect
fiber to any prescribed two-pair transversal event carrying at least one
quarter of the transversal mass. The cost is the paper's `C_d/c₀` rescaled
by `2n²` times the operational normalizer.
TEXLINE: main.tex:493-709,868-908 -/
theorem defect_mean_exchange_flow (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (hgood : ∀ index,
      (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index) / 4 ≤ w index ∧
      w index ≤ 4 * (TransversalPartition.partitionSum r o₁ o₂ q /
        FirstPhaseFailure.defectPartition r o₁ o₂ q index))
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hlarge : classMass (operationalLaw r o₁ o₂ q w hq hw) .transversal / 4 ≤
      eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤
        (8 + 32 * (n : ℝ)) * (2 * (n : ℝ) ^ 2 / classMass π .transversal) := by
  classical
  intro π κ
  let A := pairEvent i k a b
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have htype := TypeMassLowerBounds.good_type_mass_bounds r o₁ o₂ q w hn hq hgood
  have hp₀lower : 1 / (5 * (n : ℝ) ^ 2) ≤ classMass π .transversal := by
    dsimp only [π]
    rw [operational_class_mass]
    have hc := (Rat.cast_le (K := ℝ)).mpr htype.2.1
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hc
  have hp₀ : 0 < classMass π .transversal :=
    (div_pos (by norm_num) (by positivity)).trans_le hp₀lower
  have hdLower : 1 / (20 * (n : ℝ) ^ 2) ≤ classMass π (.defect i k) := by
    dsimp only [π]
    rw [operational_class_mass]
    have hc := (Rat.cast_le (K := ℝ)).mpr (htype.2.2 ⟨i, k, hik⟩)
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat,
      Rat.cast_pow, Rat.cast_natCast] using hc
  have hd : 0 < classMass π (.defect i k) :=
    (div_pos (by norm_num) (by positivity)).trans_le hdLower
  have hA : 0 < eventMass π A := (div_pos hp₀ (by norm_num)).trans_le hlarge
  let source := fun state : PairedSet n =>
    if (classifyState state).val = .defect i k then π state / classMass π (.defect i k) else 0
  let sink := fun state : PairedSet n => if state ∈ A then π state / eventMass π A else 0
  have hsource : (∑ state, source state) = 1 := by
    have heq : (∑ state, source state) = classMass π (.defect i k) / classMass π (.defect i k) := by
      change _ = (∑ state, if (classifyState state).val = .defect i k then π state else 0) / _
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro state _
      dsimp only [source]
      split_ifs <;> simp
    exact heq.trans (div_self hd.ne')
  have hsink : (∑ state, sink state) = 1 := by
    calc
      _ = ∑ state ∈ A, π state / eventMass π A := by
        dsimp only [sink]
        rw [← Finset.sum_filter]
        simp
      _ = eventMass π A / eventMass π A := by rw [← Finset.sum_div]; rfl
      _ = 1 := div_self hA.ne'
  let denseCurrent := fun state next : PairedSet n =>
    source state * sink next - source next * sink state
  have hanti : ∀ state next, denseCurrent state next = -denseCurrent next state := by
    intro state next
    dsimp only [denseCurrent]
    ring
  have hdiv : ∀ state, divergence denseCurrent state = conditionalMeanDemand π (.defect i k) A state := by
    intro state
    simp only [divergence, denseCurrent, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_mul, hsource, hsink, mul_one, one_mul]
    rfl
  -- Concrete route: the dense source-sink product above is balanced and
  -- has exactly the required divergence. Its support condition fails:
  -- at n=3 the defect {(1,false),(1,true),(2,false)} and transversal
  -- {(0,false),(1,false),(2,true)} cannot be related by a single exchange.
  -- This failure is checked in scratch/observable-poincare/NonexchangeProbe.lean.
  -- STILL OPEN: replace denseCurrent by the recursion at main.tex:511-709:
  -- maintain balanced weighted hole demands, prove the quadratic split
  -- bound and future-slot conservation, route demands in disjoint leaf
  -- cliques, and specialize the resulting cost using 4-good multipliers
  -- and the defect coefficient inequalities (main.tex:897-908).
  -- The signature step refers to the cited Bränden--Huh theorem at
  -- main.tex:332-348; no rank-weight signature API exists in the pinned
  -- libraries. The recursion and coefficient extraction are same-paper
  -- obligations, not assumptions to add to Prior.
  sorry

end CountingMatroid.Analysis.DefectMeanExchangeFlow
