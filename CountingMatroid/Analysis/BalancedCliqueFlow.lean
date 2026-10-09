import CountingMatroid.Analysis.ExchangeFlowEnergy

set_option autoImplicit false

/-!
The signed star current used at a balanced leaf clique. Its divergence is
exactly the prescribed demand, and its energy is bounded by the sum of
squared demands divided by the vertex capacities at a maximizing hub.
-/

namespace CountingMatroid.Analysis.BalancedCliqueFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- PAPER: main.tex:675-680
Send each nonhub demand toward the chosen hub. -/
noncomputable def starCurrent {α : Type*} [DecidableEq α]
    (g : α → ℝ) (hub : α) (x y : α) : ℝ :=
  (if y = hub ∧ x ≠ hub then g x else 0) -
    (if x = hub ∧ y ≠ hub then g y else 0)

/-- INTERNAL: Reversing a star edge reverses its current.
TEXLINE: main.tex:675-680 -/
theorem star_current_antisymmetric {α : Type*} [DecidableEq α]
    (g : α → ℝ) (hub x y : α) :
    starCurrent g hub x y = -starCurrent g hub y x := by
  unfold starCurrent
  ring

/-- PAPER: main.tex:675-680
Balance supplies the hub's demand automatically. -/
theorem star_current_divergence {α : Type*} [Fintype α] [DecidableEq α]
    (g : α → ℝ) (hub : α) (hbalance : ∑ x, g x = 0) (x : α) :
    divergence (starCurrent g hub) x = g x := by
  classical
  by_cases hx : x = hub
  · subst x
    have hrest : (∑ y ∈ Finset.univ.erase hub, g y) = -g hub := by
      have heq := Finset.sum_erase_add (Finset.univ : Finset α) g (Finset.mem_univ hub)
      rw [hbalance] at heq
      linarith
    simp only [divergence, starCurrent, ne_eq, not_true_eq_false, and_false,
      if_false, true_and, zero_sub, Finset.sum_neg_distrib]
    rw [← Finset.sum_filter]
    have he : Finset.univ.filter (fun y : α => y ≠ hub) = Finset.univ.erase hub := by
      ext y
      simp
    rw [he, hrest, neg_neg]
  · simp [divergence, starCurrent, hx]

/-- INTERNAL: The star uses only hub edges, and its energy counts each
nonhub edge once under the symmetric conductance convention.
TEXLINE: main.tex:675-681 -/
theorem star_current_energy {α : Type*} [Fintype α] [DecidableEq α]
    (κ : α → α → ℝ) (g : α → ℝ) (hub : α)
    (hsym : ∀ x, κ hub x = κ x hub) :
    flowEnergy κ (starCurrent g hub) =
      ∑ x ∈ Finset.univ.erase hub, (g x) ^ 2 / κ x hub := by
  classical
  have hsq (x y : α) : (starCurrent g hub x y) ^ 2 / κ x y =
      (if y = hub ∧ x ≠ hub then (g x) ^ 2 / κ x hub else 0) +
      (if x = hub ∧ y ≠ hub then (g y) ^ 2 / κ y hub else 0) := by
    by_cases hx : x = hub <;> by_cases hy : y = hub
    · subst x; subst y; simp [starCurrent]
    · subst x; simp [starCurrent, hy, hsym]
    · subst y; simp [starCurrent, hx]
    · simp [starCurrent, hx, hy]
  have he : Finset.univ.filter (fun x : α => x ≠ hub) = Finset.univ.erase hub := by
    ext x
    simp
  simp only [flowEnergy, hsq, Finset.sum_add_distrib, ite_and,
    Finset.sum_ite_irrel, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter, he]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, if_true, Finset.sum_const_zero]
  ring

/-- PAPER: main.tex:675-683
Positive hub-edge conductances bounded below by the vertex capacities
realize every balanced demand, with energy at most its weighted cost. -/
theorem star_flow {α : Type*} [Fintype α] [DecidableEq α]
    (κ : α → α → ℝ) (c g : α → ℝ) (hub : α)
    (hbalance : ∑ x, g x = 0)
    (hsym : ∀ x, κ hub x = κ x hub)
    (hc : ∀ x, 0 < c x)
    (hbound : ∀ x, x ≠ hub → c x ≤ κ x hub) :
    ∃ flow : FlowCertificate κ g,
      flow.current = starCurrent g hub ∧
      flowEnergy κ flow.current ≤ ∑ x, (g x) ^ 2 / c x := by
  classical
  have hsupport : ∀ x y, κ x y = 0 → starCurrent g hub x y = 0 := by
    intro x y hz
    by_cases hx : x = hub <;> by_cases hy : y = hub
    · subst x; subst y; simp [starCurrent]
    · subst x
      have hp := (hc y).trans_le (hbound y hy)
      rw [← hsym y, hz] at hp
      exact False.elim (lt_irrefl _ hp)
    · subst y
      have hp := (hc x).trans_le (hbound x hx)
      rw [hz] at hp
      exact False.elim (lt_irrefl _ hp)
    · simp [starCurrent, hx, hy]
  refine ⟨⟨starCurrent g hub, star_current_antisymmetric g hub,
    hsupport, star_current_divergence g hub hbalance⟩, rfl, ?_⟩
  change flowEnergy κ (starCurrent g hub) ≤ _
  rw [star_current_energy κ g hub hsym]
  calc
    _ ≤ ∑ x ∈ Finset.univ.erase hub, (g x) ^ 2 / c x := by
      apply Finset.sum_le_sum
      intro x hx
      exact div_le_div_of_nonneg_left (sq_nonneg _) (hc x)
        (hbound x (Finset.ne_of_mem_erase hx))
    _ ≤ ∑ x, (g x) ^ 2 / c x :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset _ _)
        (fun x _ _ => div_nonneg (sq_nonneg _) (hc x).le)

/-- PAPER: main.tex:675-683
The maximum vertex capacity is a valid hub for the conductance
min(cᵢ,cⱼ), and the signed star realizes every balanced clique demand. -/
theorem balanced_clique_flow {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α]
    (c g : α → ℝ) (hc : ∀ x, 0 < c x) (hbalance : ∑ x, g x = 0) :
    ∃ flow : FlowCertificate (fun x y => min (c x) (c y)) g,
      flowEnergy (fun x y => min (c x) (c y)) flow.current ≤
        ∑ x, (g x) ^ 2 / c x := by
  classical
  obtain ⟨hub, _, hmax⟩ := Finset.exists_max_image (Finset.univ : Finset α) c
    Finset.univ_nonempty
  obtain ⟨flow, _, hcost⟩ := star_flow (fun x y => min (c x) (c y)) c g hub
    hbalance (fun x => min_comm _ _) hc
    (fun x _ => by rw [min_eq_left (hmax x (Finset.mem_univ x))])
  exact ⟨flow, hcost⟩

end CountingMatroid.Analysis.BalancedCliqueFlow
