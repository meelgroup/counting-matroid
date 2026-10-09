import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.OnePairObservablePoincare
import CountingMatroid.Analysis.ConditionalDefectCoefficientBounds
import CountingMatroid.Analysis.ConditionalTransversalSplitTransport
import CountingMatroid.Analysis.ConditionalVarianceTree

set_option autoImplicit false

/-!
The paper's transversal variance estimate, isolated from the final observable
variance bookkeeping. The one-pair case is proved using the existing
constant-two Poincare estimate. The coefficient-score sink selection and
node-bound arithmetic are proved here using separate conditional-coefficient
and split-transport obligations. The adaptive variance tree, root moment
identification, and disjoint-edge charge are proved in ConditionalVarianceTree
and combined here. The parent contains no open proof; the two imported
mathematical prerequisites remain open.
-/

namespace CountingMatroid.Analysis.TransversalVarianceBound

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.ObservableProjection
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalTransversalSplitTransport
open CountingMatroid.Analysis.ConditionalVarianceTree
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

/-- INTERNAL: A finite, nonempty strict transitive relation has an element
with no outgoing relation. This avoids constructing a graph data structure
for the coefficient-score sink.
TEXLINE: main.tex:797-807 -/
theorem finite_relation_sink {α : Type*} (R : α → α → Prop)
    (hirr : ∀ i, ¬ R i i) (htrans : ∀ i j k, R i j → R j k → R i k)
    (s : Finset α) (hs : s.Nonempty) : ∃ k ∈ s, ∀ t ∈ s, ¬ R k t := by
  classical
  induction s using Finset.induction_on with
  | empty => simp at hs
  | @insert a s ha ih =>
    by_cases hne : s.Nonempty
    · obtain ⟨k, hk, hks⟩ := ih hne
      by_cases hka : R k a
      · refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
        intro t ht hat
        obtain rfl | ht := Finset.mem_insert.mp ht
        · exact hirr _ hat
        · exact hks t ht (htrans k a t hka hat)
      · refine ⟨k, Finset.mem_insert_of_mem hk, ?_⟩
        intro t ht hkt
        obtain rfl | ht := Finset.mem_insert.mp ht
        · exact hka hkt
        · exact hks t ht hkt
    · have hempty : s = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
      subst s
      refine ⟨a, Finset.mem_insert_self _ _, ?_⟩
      intro t ht
      have hta : t = a := by simpa using ht
      subst t
      exact hirr a

/-- PAPER: main.tex:790-813
The coefficient-score inequalities select an unassigned branching pair
whose outgoing scores are all at most one. -/
theorem score_sink {α : Type*} (a : α → α → ℚ)
    (s : Finset α) (hs : s.Nonempty)
    (hpair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i j * a j i ≤ 1 / 16)
    (htriangle : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
      i ≠ j → j ≠ k → i ≠ k → a i j * a j k ≤ a i k) :
    ∃ k ∈ s, ∀ t ∈ s, k ≠ t → a k t ≤ 1 := by
  classical
  let R := fun i j => i ∈ s ∧ j ∈ s ∧ i ≠ j ∧ 1 < a i j
  have hirr : ∀ i, ¬ R i i := by simp [R]
  have htrans : ∀ i j k, R i j → R j k → R i k := by
    intro i j k hij hjk
    obtain ⟨hi, hj, hneij, haij⟩ := hij
    obtain ⟨_, hk, hnejk, hajk⟩ := hjk
    have hprod : 1 < a i j * a j k := by
      nlinarith [mul_pos (sub_pos.mpr haij) (sub_pos.mpr hajk)]
    have hneik : i ≠ k := by
      rintro rfl
      have h := hpair i hi j hj hneij
      linarith
    exact ⟨hi, hk, hneik, hprod.trans_le
      (htriangle i hi j hj k hk hneij hnejk hneik)⟩
  obtain ⟨k, hk, hkt⟩ := finite_relation_sink R hirr htrans s hs
  refine ⟨k, hk, ?_⟩
  intro t ht hne
  by_contra h
  exact hkt t ht ⟨hk, ht, hne, lt_of_not_ge h⟩

/-- INTERNAL: Normalize the two-pair coefficient inequality by its positive
conditional transversal total.
TEXLINE: main.tex:790-796 -/
theorem ratio_pair (a b z : ℚ) (hz : 0 < z) (h : 4 * a * b ≤ z ^ 2) :
    (a / z) * (b / z) ≤ 1 / 4 := by
  rw [div_mul_div_comm]
  apply (div_le_iff₀ (mul_pos hz hz)).mpr
  nlinarith

/-- INTERNAL: Normalize the three-pair coefficient inequality by its
positive conditional transversal total.
TEXLINE: main.tex:790-796 -/
theorem ratio_triangle (a b c z : ℚ) (hz : 0 < z) (h : a * b ≤ z * c) :
    (a / z) * (b / z) ≤ c / z := by
  calc
    _ = a * b / z ^ 2 := by ring
    _ ≤ z * c / z ^ 2 := div_le_div_of_nonneg_right h (sq_nonneg z)
    _ = c / z := by field_simp

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
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  let NodeBound : Prop := ∀ σ : Assignment n, (∃ i, σ i = none) →
    ∃ k, σ k = none ∧
      ((transversalTotal r o₁ o₂ q (Function.update σ k (some false)) : ℝ) *
        (transversalTotal r o₁ o₂ q (Function.update σ k (some true)) : ℝ) /
        (transversalTotal r o₁ o₂ q σ : ℝ)) *
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
          (1 + 8 * (n : ℝ)) * (Z * (2 * (n : ℝ) ^ 2) * nodeEnergy κ H σ)
  have hnode : NodeBound := by
    intro σ hremaining
    let s := Finset.univ.filter (fun i => σ i = none)
    have hmem (i : Fin n) : i ∈ s ↔ σ i = none := by simp [s]
    have hs : s.Nonempty := by
      obtain ⟨i, hi⟩ := hremaining
      exact ⟨i, (hmem i).mpr hi⟩
    let z := transversalTotal r o₁ o₂ q σ
    let C := TransversalPartition.partitionSum r o₁ o₂ q
    let c := defectTotal r o₁ o₂ q σ
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    have hz : 0 < z := transversal_total_pos r o₁ o₂ q hq σ
    have hC : 0 < C := by
      dsimp only [C]
      rw [← transversal_total_empty r o₁ o₂ q]
      exact transversal_total_pos r o₁ o₂ q hq _
    have hc (index : DefectIndex n) (he : σ index.emptyPair = none)
        (hf : σ index.fullPair = none) : 0 < c index :=
      defect_total_pos r o₁ o₂ q hq σ index he hf
    have hD (index : DefectIndex n) : 0 < D index :=
      DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq index
    obtain ⟨hcp, hct⟩ :=
      ConditionalDefectCoefficientBounds.conditional_defect_coefficient_bounds
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone σ
    obtain ⟨hDp, hDt⟩ :=
      ConditionalDefectCoefficientBounds.conditional_defect_coefficient_bounds
        n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone (fun _ => none)
    simp only [defect_total_empty, transversal_total_empty] at hDp hDt
    let a := fun i j : Fin n => if hij : i ≠ j then
      (c ⟨i, j, hij⟩ / z) * (D ⟨j, i, hij.symm⟩ / C) else 0
    have hscorePair : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → a i j * a j i ≤ 1 / 16 := by
      intro i hi j hj hij
      have hiσ := (hmem i).mp hi
      have hjσ := (hmem j).mp hj
      have hpcond := ratio_pair _ _ _ hz (hcp i j hij hiσ hjσ)
      have hpglobal := ratio_pair _ _ _ hC (hDp j i hij.symm True.intro True.intro)
      dsimp only [a]
      rw [dif_pos hij, dif_pos hij.symm]
      calc
        _ = ((c ⟨i, j, hij⟩ / z) * (c ⟨j, i, hij.symm⟩ / z)) *
          ((D ⟨j, i, hij.symm⟩ / C) * (D ⟨i, j, hij⟩ / C)) := by ring
        _ ≤ (1 / 4 : ℚ) * (1 / 4) :=
          mul_le_mul hpcond hpglobal
            (mul_nonneg (div_pos (hD _) hC).le (div_pos (hD _) hC).le)
            (by norm_num)
        _ = 1 / 16 := by norm_num
    have hscoreTriangle : ∀ i ∈ s, ∀ j ∈ s, ∀ k ∈ s,
        i ≠ j → j ≠ k → i ≠ k → a i j * a j k ≤ a i k := by
      intro i hi j hj k hk hij hjk hik
      have hiσ := (hmem i).mp hi
      have hjσ := (hmem j).mp hj
      have hkσ := (hmem k).mp hk
      have htcond := ratio_triangle _ _ _ _ hz (hct i j k hij hjk hik hiσ hjσ hkσ)
      have htglobal := ratio_triangle _ _ _ _ hC (hDt k j i hjk.symm hij.symm hik.symm True.intro True.intro True.intro)
      dsimp only [a]
      rw [dif_pos hij, dif_pos hjk, dif_pos hik]
      calc
        _ = ((c ⟨i, j, hij⟩ / z) * (c ⟨j, k, hjk⟩ / z)) *
          ((D ⟨k, j, hjk.symm⟩ / C) * (D ⟨j, i, hij.symm⟩ / C)) := by ring
        _ ≤ (c ⟨i, k, hik⟩ / z) * (D ⟨k, i, hik.symm⟩ / C) :=
          mul_le_mul htcond htglobal
            (mul_nonneg (div_pos (hD _) hC).le (div_pos (hD _) hC).le)
            (div_pos (hc _ hiσ hkσ) hz).le
        _ = _ := rfl
    obtain ⟨k, hk, hsink⟩ := score_sink a s hs hscorePair hscoreTriangle
    have hkσ := (hmem k).mp hk
    refine ⟨k, hkσ, ?_⟩
    have hterm (t : Fin n) (h : σ t = none ∧ t ≠ k) :
        (c ⟨k, t, h.2.symm⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) ≤ 4 * (z : ℝ) := by
      have hscore := hsink t ((hmem t).mpr h.1) h.2.symm
      dsimp only [a] at hscore
      rw [dif_pos h.2.symm] at hscore
      have hprod : c ⟨k, t, h.2.symm⟩ * D ⟨t, k, h.2⟩ ≤ z * C := by
        have h := (div_le_iff₀ (mul_pos hz hC)).mp
          (by simpa only [div_mul_div_comm, one_mul] using hscore)
        simpa using h
      have hgood' : C ≤ 4 * w ⟨t, k, h.2⟩ * D ⟨t, k, h.2⟩ := by
        have hscaled := (div_le_iff₀ (by norm_num : (0 : ℚ) < 4)).mp (hgood ⟨t, k, h.2⟩).1
        have h' := (div_le_iff₀ (hD ⟨t, k, h.2⟩)).mp hscaled
        nlinarith
      have hbound : c ⟨k, t, h.2.symm⟩ / w ⟨t, k, h.2⟩ ≤ 4 * z := by
        apply (div_le_iff₀ (hw _)).mpr
        apply le_of_mul_le_mul_right _ (hD ⟨t, k, h.2⟩)
        calc
          _ ≤ z * C := hprod
          _ ≤ z * (4 * w ⟨t, k, h.2⟩ * D ⟨t, k, h.2⟩) :=
            mul_le_mul_of_nonneg_left hgood' hz.le
          _ = _ := by ring
      exact_mod_cast hbound
    have hsum : (∑ t : Fin n, if h : σ t = none ∧ t ≠ k then
        (c ⟨k, t, h.2.symm⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
          (n : ℝ) * (4 * (z : ℝ)) := by
      calc
        _ ≤ ∑ _t : Fin n, 4 * (z : ℝ) := by
          apply Finset.sum_le_sum
          intro t _
          split_ifs with h
          · exact hterm t h
          · exact mul_nonneg (by norm_num) (by exact_mod_cast hz.le)
        _ = _ := by simp
    have hκ : ∀ state next, 0 ≤ κ state next := fun state next =>
      mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
        (le_min (π.coe_nonneg state) (π.coe_nonneg next))
    have hEσ : 0 ≤ nodeEnergy κ H σ := by
      apply mul_nonneg (by norm_num)
      apply Finset.sum_nonneg
      intro state _
      apply Finset.sum_nonneg
      intro next _
      split_ifs
      · exact mul_nonneg (hκ _ _) (sq_nonneg _)
      · exact le_rfl
    have hZ : 0 < Z := by
      dsimp only [Z]
      exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
        r o₁ o₂ q 1 w hq hw).1
    have hzreal : (0 : ℝ) < z := by exact_mod_cast hz
    have hcoef : 1 + 2 / (z : ℝ) *
        (∑ t : Fin n, if h : σ t = none ∧ t ≠ k then
          (c ⟨k, t, h.2.symm⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) ≤
            1 + 8 * (n : ℝ) := by
      have h := mul_le_mul_of_nonneg_left hsum
        (show (0 : ℝ) ≤ 2 / (z : ℝ) from div_nonneg (by norm_num) hzreal.le)
      have hcancel : 2 / (z : ℝ) * ((n : ℝ) * (4 * (z : ℝ))) = 8 * (n : ℝ) := by
        field_simp
        norm_num
      rw [hcancel] at h
      linarith
    have htransport := conditional_transversal_split_transport n r M₁ M₂ o₁ o₂
      q w hn hfull hr h₁ h₂ hq hqone hw σ k hkσ H
    exact htransport.trans (mul_le_mul_of_nonneg_right hcoef
      (mul_nonneg (mul_nonneg hZ.le (by positivity)) hEσ))
  have hκ : ∀ state next, 0 ≤ κ state next := fun state next =>
    mul_nonneg ((exchangeProposal n hn).coe_nonneg state next)
      (le_min (π.coe_nonneg state) (π.coe_nonneg next))
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities
      r o₁ o₂ q 1 w hq hw).1
  let K := (1 + 8 * (n : ℝ)) * (Z * (2 * (n : ℝ) ^ 2))
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have ht := adaptive_conditional_moment_bound r o₁ o₂ q hq κ hκ H K hK
    (by
      intro σ hremaining
      obtain ⟨k, hk, hb⟩ := hnode σ hremaining
      refine ⟨k, hk, ?_⟩
      simpa only [K, mul_assoc] using hb) (fun _ => none)
  have hcount : (unassigned (n := n) (fun _ => none)).card = n := by simp [unassigned]
  rw [root_conditional_moment r o₁ o₂ q w hq hw H, node_energy_empty, hcount] at ht
  apply le_of_mul_le_mul_left _ hZ
  calc
    _ ≤ (n : ℝ) * K * potentialEnergy κ H := ht
    _ = _ := by dsimp only [K]; ring

end CountingMatroid.Analysis.TransversalVarianceBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · parent-closed · proved adaptive variance telescoping, fully assigned leaves, restricted-energy splitting and the operational root bridge; combined them with the node estimate to remove the parent hole. Two substantial imported coefficient/transport obligations remain open for live handoff.
* 2026-10-09 · decomposed · defined operational conditional totals and proved positivity and splitting; proved score-sink selection and all node-bound arithmetic, using separate conditional coefficient and split-transport children. The parent hole is now adaptive-tree variance telescoping and disjoint-depth energy charging.
* recovery · partial · proved the supported-law variance bridge and the n=1 branch; exposed the n≥2 centered moment after positive-mass cancellation. Conditional coefficient bounds (397-449) and slot transport (455-709) are missing local lemmas; no new open helper was introduced.
-/
