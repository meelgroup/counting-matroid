import CountingMatroid.Analysis.ExchangeFlowEnergy

set_option autoImplicit false

/-!
The potential estimate at a leaf of the paper's balanced-hole recursion.
At a maximum-weight hub, weighted Cauchy--Schwarz bounds a balanced
demand pairing using only incident edge energies. This module proves the
resulting pairing bound; it does not assemble
leaf demands across the recursion.
-/

namespace CountingMatroid.Analysis.BalancedCliqueEnergy

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: At a maximum-weight hub, the sum of incident edge energies
is bounded by the unoriented energy of the whole clique.
TEXLINE: main.tex:670-683 -/
theorem hub_energy_le {α : Type*} [Fintype α] [DecidableEq α]
    (c H : α → ℝ) (hc : ∀ i, 0 ≤ c i) (hub : α)
    (hmax : ∀ i, c i ≤ c hub) :
    (∑ i, c i * (H i - H hub) ^ 2) ≤
      potentialEnergy (fun i j => min (c i) (c j)) H := by
  classical
  let E := fun i j => min (c i) (c j) * (H i - H j) ^ 2
  have hnn : ∀ i j, 0 ≤ E i j := fun i j =>
    mul_nonneg (le_min (hc i) (hc j)) (sq_nonneg _)
  have hsym : ∀ i j, E i j = E j i := by
    intro i j
    dsimp only [E]
    rw [min_comm]
    ring
  have hdiag : E hub hub = 0 := by simp [E]
  have hstar : (∑ i, c i * (H i - H hub) ^ 2) = ∑ i, E hub i := by
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym]
    simp only [E, min_eq_left (hmax i)]
  have hrest : (∑ i ∈ Finset.univ.erase hub, E hub i) = ∑ i, E hub i := by
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ hub), hdiag, add_zero]
  have hbound : 2 * (∑ i, E hub i) ≤ ∑ i, ∑ j, E i j := by
    have htotal : (∑ i, ∑ j, E i j) =
        (∑ i ∈ Finset.univ.erase hub, ∑ j, E i j) + ∑ j, E hub j := by
      exact (Finset.sum_erase_add _ _ (Finset.mem_univ hub)).symm
    rw [htotal]
    have hr : (∑ i, E hub i) ≤ ∑ i ∈ Finset.univ.erase hub, ∑ j, E i j := by
      rw [← hrest]
      apply Finset.sum_le_sum
      intro i _
      rw [hsym hub i]
      exact Finset.single_le_sum (fun j _ => hnn i j) (Finset.mem_univ hub)
    linarith
  rw [hstar]
  change _ ≤ (1 / 2 : ℝ) * ∑ i, ∑ j, E i j
  linarith

/-- INTERNAL: The paper's leaf-clique routing bounds a balanced demand's
squared potential pairing by its weighted demand cost times clique energy.
TEXLINE: main.tex:670-683 -/
theorem balanced_clique_pairing_sq_le {α : Type*} [Fintype α] [DecidableEq α]
    (c g H : α → ℝ) (hc : ∀ i, 0 < c i)
    (hbalance : ∑ i, g i = 0) (hub : α) (hmax : ∀ i, c i ≤ c hub) :
    (∑ i, g i * H i) ^ 2 ≤
      (∑ i, (g i) ^ 2 / c i) *
        potentialEnergy (fun i j => min (c i) (c j)) H := by
  have hshift : (∑ i, g i * (H i - H hub)) = ∑ i, g i * H i := by
    simp only [mul_sub, Finset.sum_sub_distrib, ← Finset.sum_mul, hbalance,
      zero_mul, sub_zero]
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset α))
    (r := fun i => g i * (H i - H hub))
    (f := fun i => (g i) ^ 2 / c i)
    (g := fun i => c i * (H i - H hub) ^ 2)
    (fun i _ => div_nonneg (sq_nonneg _) (hc i).le)
    (fun i _ => mul_nonneg (hc i).le (sq_nonneg _)) (by
      intro i _
      exact le_of_eq (by field_simp [(hc i).ne']))
  rw [hshift] at hcs
  exact hcs.trans (mul_le_mul_of_nonneg_left
    (hub_energy_le c H (fun i => (hc i).le) hub hmax)
    (Finset.sum_nonneg (fun i _ => div_nonneg (sq_nonneg _) (hc i).le)))

end CountingMatroid.Analysis.BalancedCliqueEnergy
