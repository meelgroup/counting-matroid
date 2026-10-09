import CountingMatroid.Analysis.DefectSlotRoot
import CountingMatroid.Analysis.DefectSlotFutureBound

set_option autoImplicit false

/-!
Normalize the iterated two-hole potential estimate into the defect/event
mass bound. Root future entries are bounded by full defect partitions.
-/

namespace CountingMatroid.Analysis.DefectSlotBudget

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion

/-- INTERNAL: The exact mass and partition normalization of the paper's
root potential bound, before any goodness assumption is imposed.
TEXLINE: main.tex:652-665,875-898 -/
theorem defect_slot_budget {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let B : PairedSet n := {(k, !b)}
    let U : Finset (Fin n) := (Finset.univ.erase i).erase k
    let p : PairedGround n := (i, !a)
    let d : PairedGround n := (k, b)
    let W : PairedGround n → ℝ := fun hole =>
      if hole.1 = i then (w ⟨i, k, hik⟩ : ℝ)
      else if h : hole.1 = k then 1 else (w ⟨hole.1, k, h⟩ : ℝ)
    let root := twoHoleRoot r o₁ o₂ q B U p d
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    let C : ℝ := (2 * (n : ℝ) ^ 2) * (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
    C * (nodePotential r o₁ o₂ q B U W root -
      ∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
        (2 * (n : ℝ) ^ 2) *
          (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
            (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
              ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
  classical
  intro π B U p d W root D C
  let Z : ℝ := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
  let Dik : ℝ := (D ⟨i, k, hik⟩ : ℝ)
  let E := eventMass π (pairEvent i k a b)
  let S := ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
    (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0
  let coefficient := 2 / (Dik * Z * E)
  obtain ⟨hZq, _, _, hdef⟩ :=
    StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hZ : 0 < Z := by dsimp only [Z]; exact_mod_cast hZq
  have hDik : 0 < Dik := by
    dsimp only [Dik, D]
    rw [← DefectSlotRoot.source_slot_total r o₁ o₂ q i k hik a b]
    exact slot_total_pos r o₁ o₂ q hq _ _ _ _
  have hE : 0 < E := hA
  have hwi : (0 : ℝ) < (w ⟨i, k, hik⟩ : ℝ) := by exact_mod_cast hw ⟨i, k, hik⟩
  have hpd : p ≠ d := fun he => hik (congrArg Prod.fst he)
  have hsp : slotTotal r o₁ o₂ q B {p, d} U p = Dik :=
    DefectSlotRoot.source_slot_total r o₁ o₂ q i k hik a b
  have hsd : slotTotal r o₁ o₂ q B {p, d} U d = Z * E :=
    DefectSlotRoot.event_slot_total r o₁ o₂ q w hq hw i k hik a b
  have hWp : W p = (w ⟨i, k, hik⟩ : ℝ) := by simp [W, p]
  have hWd : W d = 1 := by simp [W, d, Ne.symm hik]
  have hmass : classMass π (.defect i k) = (w ⟨i, k, hik⟩ : ℝ) * Dik / Z := by
    dsimp only [π]
    rw [operational_class_mass, hdef ⟨i, k, hik⟩]
    simp only [Rat.cast_div, Rat.cast_mul]
    rfl
  have hrootCost : C * nodePotential r o₁ o₂ q B U W root =
      (2 * (n : ℝ) ^ 2) * (1 / classMass π (.defect i k) + 1 / E) := by
    rw [SlotTransportFlow.two_hole_potential r o₁ o₂ q hq B U p d hpd W,
      hsp, hsd, hWp, hWd, hmass]
    change ((2 * (n : ℝ) ^ 2) * Z) * (1 / (Dik * (w ⟨i, k, hik⟩ : ℝ)) +
      1 / ((Z * E) * 1)) = _
    field_simp [hZ.ne', hDik.ne', hE.ne', hwi.ne']
    <;> ring
  have hcoefficient : 0 ≤ coefficient := (div_pos (by norm_num)
    (mul_pos (mul_pos hDik hZ) hE)).le
  have hS : (∑ t ∈ U, if h : t ≠ i ∧ t ≠ k then
      (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) = S := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro t _ ht
    have hneg : ¬ (t ≠ i ∧ t ≠ k) := by
      intro hh
      exact ht (by simp [U, hh.1, hh.2])
    rw [dif_neg hneg]
  have hfutureBound : -(∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false)) ≤
      coefficient * S := by
    calc
      _ = ∑ t ∈ U, -(nodeFuture r o₁ o₂ q B U root t / W (t, false)) :=
        by rw [Finset.sum_neg_distrib]
      _ ≤ ∑ t ∈ U, coefficient * (if h : t ≠ i ∧ t ≠ k then
          (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
        apply Finset.sum_le_sum
        intro t ht
        have htk : t ≠ k := (Finset.mem_erase.mp ht).1
        have hti : t ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp ht).2).1
        have hwt : W (t, false) = (w ⟨t, k, htk⟩ : ℝ) := by
          simp only [W, if_neg hti, dif_neg htk]
        have hwpos : (0 : ℝ) < (w ⟨t, k, htk⟩ : ℝ) := by exact_mod_cast hw _
        rw [SlotTransportFlow.two_hole_future r o₁ o₂ q B U p d hpd t,
          hsp, hsd, hwt, dif_pos ⟨hti, htk⟩]
        calc
          _ = coefficient * (futureMatrix r o₁ o₂ q B {p, d} U t p d /
              (w ⟨t, k, htk⟩ : ℝ)) := by dsimp only [coefficient]; ring
          _ ≤ _ := mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right
              (DefectSlotFutureBound.root_future_le_defect_partition r o₁ o₂ q hq
                i t k hti.symm htk hik a b) hwpos.le) hcoefficient
      _ = coefficient * S := by rw [← Finset.mul_sum, hS]
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hscale : C * coefficient = (2 * (n : ℝ) ^ 2) * (2 / (Dik * E)) := by
    change ((2 * (n : ℝ) ^ 2) * Z) * (2 / (Dik * Z * E)) = _
    field_simp [hZ.ne']
  calc
    _ = C * nodePotential r o₁ o₂ q B U W root +
        C * (-(∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false))) := by ring
    _ = (2 * (n : ℝ) ^ 2) * (1 / classMass π (.defect i k) + 1 / E) +
        C * (-(∑ t ∈ U, nodeFuture r o₁ o₂ q B U root t / W (t, false))) := by rw [hrootCost]
    _ ≤ (2 * (n : ℝ) ^ 2) * (1 / classMass π (.defect i k) + 1 / E) +
        C * (coefficient * S) := add_le_add le_rfl (mul_le_mul_of_nonneg_left hfutureBound hC)
    _ = _ := by rw [← mul_assoc, hscale]; ring

end CountingMatroid.Analysis.DefectSlotBudget
