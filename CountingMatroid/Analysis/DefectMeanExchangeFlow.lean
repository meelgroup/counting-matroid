import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.DefectPartitionTriangle
import CountingMatroid.Analysis.DefectTransportRaw

set_option autoImplicit false

/-!
The signed exchange-current bound for the paper's defect-mean transport.
The numerical specialization of goodness and the large-event assumption is
proved here. The remaining mathematical obligations are the three-pair
coefficient inequality in `DefectPartitionTriangle` and the recursive
flow construction in `DefectTransportRaw`; both are imported and used.
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
  -- Previous concrete route, retained in DefectTransportRaw: the dense
  -- source-sink product has the right divergence but fails exchange support.
  -- At n=3 the defect {(1,false),(1,true),(2,false)} and transversal
  -- {(0,false),(1,false),(2,true)} cannot be related by a single exchange.
  -- The prior check is scratch/observable-poincare/NonexchangeProbe.lean.
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
  let D := fun index : DefectIndex n =>
    (FirstPhaseFailure.defectPartition r o₁ o₂ q index : ℝ)
  let C : ℝ := TransversalPartition.partitionSum r o₁ o₂ q
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  have hD (index : DefectIndex n) : 0 < D index := by
    dsimp only [D]
    exact_mod_cast DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
  obtain ⟨hZq, hzero, _, hdefect⟩ :=
    StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast hZq
  have hzeroReal : classMass π .transversal = C / Z := by
    dsimp only [π]
    rw [operational_class_mass, hzero]
    simp only [Rat.cast_div]
    rfl
  have hdefectReal : classMass π (.defect i k) = (w ⟨i, k, hik⟩ : ℝ) * D ⟨i, k, hik⟩ / Z := by
    dsimp only [π]
    rw [operational_class_mass, hdefect ⟨i, k, hik⟩]
    simp only [Rat.cast_div, Rat.cast_mul]
    rfl
  have hgoodReal (index : DefectIndex n) : C ≤ 4 * (w index : ℝ) * D index := by
    have h : (C / D index) / 4 ≤ (w index : ℝ) := by
      dsimp only [C, D]
      exact_mod_cast (hgood index).1
    have h' := (div_le_iff₀ (by norm_num : (0 : ℝ) < 4)).mp h
    have h'' := (div_le_iff₀ (hD index)).mp h'
    nlinarith
  have hmass : classMass π .transversal / 4 ≤ classMass π (.defect i k) := by
    rw [hzeroReal, hdefectReal]
    calc
      (C / Z) / 4 = (C / 4) / Z := by ring
      _ ≤ (w ⟨i, k, hik⟩ : ℝ) * D ⟨i, k, hik⟩ / Z :=
        div_le_div_of_nonneg_right (by nlinarith [hgoodReal ⟨i, k, hik⟩]) hZ.le
  have hbase : 1 / classMass π (.defect i k) ≤ 4 / classMass π .transversal := by
    apply (div_le_div_iff₀ hd hp₀).mpr
    nlinarith [hmass]
  have hevent : 1 / eventMass π A ≤ 4 / classMass π .transversal := by
    apply (div_le_div_iff₀ hA hp₀).mpr
    nlinarith [hlarge]
  have hterm (t : Fin n) (h : t ≠ i ∧ t ≠ k) :
      D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) ≤ 4 * D ⟨i, k, hik⟩ := by
    have hwreal : 0 < (w ⟨t, k, h.2⟩ : ℝ) := by exact_mod_cast hw ⟨t, k, h.2⟩
    have htri : D ⟨i, t, Ne.symm h.1⟩ * D ⟨t, k, h.2⟩ ≤ C * D ⟨i, k, hik⟩ := by
      dsimp only [D, C]
      exact_mod_cast DefectPartitionTriangle.defect_partition_triangle
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone i t k (Ne.symm h.1) h.2 hik
    apply (div_le_iff₀ hwreal).mpr
    apply le_of_mul_le_mul_right _ (hD ⟨t, k, h.2⟩)
    calc
      D ⟨i, t, Ne.symm h.1⟩ * D ⟨t, k, h.2⟩ ≤ C * D ⟨i, k, hik⟩ := htri
      _ ≤ (4 * (w ⟨t, k, h.2⟩ : ℝ) * D ⟨t, k, h.2⟩) * D ⟨i, k, hik⟩ :=
        mul_le_mul_of_nonneg_right (hgoodReal ⟨t, k, h.2⟩) (hD ⟨i, k, hik⟩).le
      _ = (4 * D ⟨i, k, hik⟩ * (w ⟨t, k, h.2⟩ : ℝ)) * D ⟨t, k, h.2⟩ := by ring
  have hsum : (∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
      D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
        (n : ℝ) * (4 * D ⟨i, k, hik⟩) := by
    calc
      _ ≤ ∑ _t : Fin n, 4 * D ⟨i, k, hik⟩ := by
        apply Finset.sum_le_sum
        intro t _
        split_ifs with h
        · exact hterm t h
        · exact mul_nonneg (by norm_num) (hD ⟨i, k, hik⟩).le
      _ = _ := by simp
  have hextra : (2 / (D ⟨i, k, hik⟩ * eventMass π A)) *
      (∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
        D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
          32 * (n : ℝ) / classMass π .transversal := by
    calc
      _ ≤ (2 / (D ⟨i, k, hik⟩ * eventMass π A)) *
          ((n : ℝ) * (4 * D ⟨i, k, hik⟩)) :=
        mul_le_mul_of_nonneg_left hsum
          (div_nonneg (by norm_num) (mul_pos (hD ⟨i, k, hik⟩) hA).le)
      _ = 8 * (n : ℝ) / eventMass π A := by
        field_simp [(hD ⟨i, k, hik⟩).ne', hA.ne']
        ring
      _ ≤ 32 * (n : ℝ) / classMass π .transversal := by
        apply (div_le_div_iff₀ hA hp₀).mpr
        have h := mul_le_mul_of_nonneg_left hlarge
          (by positivity : (0 : ℝ) ≤ 32 * (n : ℝ))
        nlinarith
  obtain ⟨flow, hflow⟩ := DefectTransportRaw.defect_transport_raw
    n r M₁ M₂ o₁ o₂ q w hn hfull hr h₁ h₂ hq hqone hw i k hik a b hA
  refine ⟨flow, hflow.trans ?_⟩
  change (2 * (n : ℝ) ^ 2) *
    (1 / classMass π (.defect i k) + 1 / eventMass π A +
      (2 / (D ⟨i, k, hik⟩ * eventMass π A)) *
        ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
          D ⟨i, t, Ne.symm h.1⟩ / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤ _
  calc
    _ ≤ (2 * (n : ℝ) ^ 2) *
        (4 / classMass π .transversal + 4 / classMass π .transversal +
          32 * (n : ℝ) / classMass π .transversal) :=
      mul_le_mul_of_nonneg_left (add_le_add (add_le_add hbase hevent) hextra) (by positivity)
    _ = _ := by ring

end CountingMatroid.Analysis.DefectMeanExchangeFlow

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · handoff accepted · Lean validated semantic use of both children and the scheduler took ownership under request `defect-flow-split-20261009-01`; the parent numerical proof has no local gap, while both child proofs remain open.
* 2026-10-09 · decomposed · proved the entire numerical specialization through two separately elaborated children: the unconditional three-pair coefficient inequality and the recursive transport bound before goodness. Retained the balanced product-current attempt in `DefectTransportRaw`; its exchange-support obstruction still requires the recursive leaf flow. Live handoff requested under OPEN guidance.
-/
