import CountingMatroid.Analysis.ObservableProjection

set_option autoImplicit false

/-!
The dual energy inequality used by the stationary time-average estimate.
Orthogonality is expressed through the actual weighted classifier fibers,
including zero-mass fibers and invalid states.
-/
namespace CountingMatroid.Analysis.ObservableEnergyDual

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableProjection
open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

/-- INTERNAL: Defect-fiber averaging preserves inner products with functions
constant on each defect fiber; transversal values are retained.
TEXLINE: main.tex:982-988 -/
theorem projected_inner_product {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (G H : PairedSet n → ℝ) (c : Fin n → Fin n → ℝ)
    (hG : ∀ i k state, (classifyState state).val = .defect i k → G state = c i k) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    ip π G H = ip π G (observableProjection π H) := by
  classical
  intro π
  have hzero (state : PairedSet n) (hk : (classifyState state).val = .invalid) :
      π state = 0 := by
    simp [π, operationalLaw, StationaryMeanIdentities.stateWeight, hk, weightOfKind]
  have hsplit (F : PairedSet n → ℝ) : ip π G F =
      (∑ state : PairedSet n, if (classifyState state).val = .transversal then
        π state * G state * F state else 0) +
      ∑ i : Fin n, ∑ k : Fin n, ∑ state : PairedSet n,
        if (classifyState state).val = .defect i k then
          π state * G state * F state else 0 := by
    have hcell (state : PairedSet n) : π state * G state * F state =
        (if (classifyState state).val = .transversal then
          π state * G state * F state else 0) +
        ∑ i : Fin n, ∑ k : Fin n,
          if (classifyState state).val = .defect i k then
            π state * G state * F state else 0 := by
      cases hk : (classifyState state).val with
      | invalid => simp [hk, hzero state hk]
      | transversal => simp [hk]
      | defect i k => simp [hk, ite_and]
    unfold ip
    rw [Finset.sum_congr rfl (fun state _ => hcell state), Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    exact Finset.sum_comm
  rw [hsplit H, hsplit (observableProjection π H)]
  congr 1
  · apply Finset.sum_congr rfl
    intro state _
    split_ifs with hk
    · simp [observableProjection, hk]
    · rfl
  · apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro k _
    let mass := ∑ state : PairedSet n,
      if (classifyState state).val = .defect i k then π state else 0
    let num := ∑ state : PairedSet n,
      if (classifyState state).val = .defect i k then π state * H state else 0
    have hleft : (∑ state : PairedSet n,
        if (classifyState state).val = .defect i k then
          π state * G state * H state else 0) = c i k * num := by
      simp only [num, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state _
      split_ifs with hk
      · rw [hG i k state hk]; ring
      · ring
    have hright : (∑ state : PairedSet n,
        if (classifyState state).val = .defect i k then
          π state * G state * observableProjection π H state else 0) =
        c i k * (num / mass) * mass := by
      simp only [mass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state _
      split_ifs with hk
      · rw [hG i k state hk]
        simp only [observableProjection, hk]
        change π state * c i k * (num / mass) = _
        ring
      · ring
    rw [hleft, hright]
    by_cases hm : mass = 0
    · have hnum : num = 0 := by
        apply Finset.sum_eq_zero
        intro state _
        split_ifs with hk
        · have hs := Finset.single_le_sum
            (s := Finset.univ) (a := state)
            (f := fun next : PairedSet n =>
              if (classifyState next).val = .defect i k then π next else 0)
            (fun next _ => by split_ifs; exact π.coe_nonneg next; exact le_rfl)
            (Finset.mem_univ state)
          simp only [hk, if_true] at hs
          change π state ≤ mass at hs
          have hz : π state = 0 := le_antisymm (by simpa [hm] using hs) (π.coe_nonneg state)
          rw [hz, zero_mul]
        · rfl
      simp [hnum, hm]
    · field_simp

/-- INTERNAL: Restricted observable Poincare control gives the centered
observable's dual energy bound. No full-support assumption is required.
TEXLINE: main.tex:982-990 -/
theorem observable_energy_dual {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (P : FinChain (PairedSet n)) (G : PairedSet n → ℝ)
    (c : Fin n → Fin n → ℝ)
    (hG : ∀ i k state, (classifyState state).val = .defect i k → G state = c i k)
    (K : ℝ) (henergy : ∀ H,
      Var (operationalLaw r o₁ o₂ q w hq hw)
        (observableProjection (operationalLaw r o₁ o₂ q w hq hw) H) ≤
      K * dirichlet (operationalLaw r o₁ o₂ q w hq hw) P H H) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    ∀ H, (ip π (fun x => G x - Ex π G) H) ^ 2 ≤
      (K * Var π G) * dirichlet π P H H := by
  intro π H
  let g := fun x => G x - Ex π G
  have hg : Ex π g = 0 := Ex_center π G
  have hp := projected_inner_product r o₁ o₂ q w hq hw g H
    (fun i k => c i k - Ex π G) (by
      intro i k state hk
      dsimp only [g]
      rw [hG i k state hk])
  change ip π g H = ip π g (observableProjection π H) at hp
  have hc : ip π g (observableProjection π H) =
      ip π g (fun x => observableProjection π H x - Ex π (observableProjection π H)) := by
    have hsub : ip π g (fun x => observableProjection π H x - Ex π (observableProjection π H)) =
        ip π g (observableProjection π H) - Ex π (observableProjection π H) * Ex π g := by
      simp only [ip, Ex, Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro x _
      ring
    rw [hsub, hg, mul_zero, sub_zero]
  rw [hp, hc]
  have hb := ip_sq_le π g
    (fun x => observableProjection π H x - Ex π (observableProjection π H))
  rw [← Var_eq_ip_center, ← Var_eq_ip_center] at hb
  refine hb.trans ?_
  have he := mul_le_mul_of_nonneg_left (henergy H) (Var_nonneg π G)
  convert he using 1 <;> ring

end CountingMatroid.Analysis.ObservableEnergyDual
