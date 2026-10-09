import CountingMatroid.Analysis.ExchangeFlowEnergy

set_option autoImplicit false

/-!
Embed a finite signed flow into a larger state space. Injectivity preserves
its divergence, support, and energy, including zero conductances.
-/

namespace CountingMatroid.Analysis.EmbeddedFlow

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: Extend a current by zero outside the image of its vertices.
TEXLINE: main.tex:670-683 -/
noncomputable def embeddedCurrent {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (J : α → α → ℝ) (s t : β) : ℝ :=
  ∑ x, ∑ y, if v x = s ∧ v y = t then J x y else 0

/-- INTERNAL: Injectivity recovers the original current on embedded vertices.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_apply {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (hv : Function.Injective v) (J : α → α → ℝ) (x y : α) :
    embeddedCurrent v J (v x) (v y) = J x y := by
  classical
  simp [embeddedCurrent, hv.eq_iff, ite_and]

/-- INTERNAL: An extended current vanishes if either endpoint is outside
its embedded vertex set.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_off_image {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (J : α → α → ℝ) (s t : β)
    (hoff : (∀ x, v x ≠ s) ∨ (∀ y, v y ≠ t)) : embeddedCurrent v J s t = 0 := by
  rcases hoff with hs | ht
  · simp [embeddedCurrent, hs]
  · simp [embeddedCurrent, ht]

/-- INTERNAL: Extending an antisymmetric current preserves antisymmetry.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_antisymmetric {α β : Type*} [Fintype α] [DecidableEq β]
    (v : α → β) (J : α → α → ℝ) (hJ : ∀ x y, J x y = -J y x) (s t : β) :
    embeddedCurrent v J s t = -embeddedCurrent v J t s := by
  classical
  unfold embeddedCurrent
  rw [Finset.sum_comm]
  simp only [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro y _
  rw [hJ]
  simp only [and_comm]
  split_ifs <;> simp

/-- INTERNAL: Embedding pushes the divergence to the corresponding state
without creating any demand outside the image.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_divergence {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (v : α → β) (J : α → α → ℝ) (s : β) :
    divergence (embeddedCurrent v J) s =
      ∑ x, if v x = s then divergence J x else 0 := by
  classical
  unfold divergence embeddedCurrent
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  simp only [ite_and, Finset.sum_ite_irrel, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, Finset.sum_const_zero]

/-- INTERNAL: Reindex a function supported on an injective finite image.
TEXLINE: main.tex:670-683 -/
private theorem sum_supported_image {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (v : α → β) (hv : Function.Injective v) (f : β → ℝ)
    (hoff : ∀ s, (∀ x, v x ≠ s) → f s = 0) :
    (∑ s, f s) = ∑ x, f (v x) := by
  classical
  have hsum : (∑ s ∈ Finset.univ.image v, f s) = ∑ s, f s := by
    apply Finset.sum_subset (Finset.subset_univ _)
    intro s _ hs
    apply hoff s
    intro x hx
    exact hs (Finset.mem_image.mpr ⟨x, Finset.mem_univ x, hx⟩)
  rw [← hsum, Finset.sum_image (fun x _ y _ h => hv h)]

/-- INTERNAL: Extending a current preserves its unoriented energy when
conductances agree on the embedded vertices.
TEXLINE: main.tex:670-683 -/
theorem embedded_current_energy {α β : Type*} [Fintype α] [Fintype β]
    [DecidableEq β] (v : α → β) (hv : Function.Injective v)
    (κ : β → β → ℝ) (J : α → α → ℝ) :
    flowEnergy κ (embeddedCurrent v J) =
      flowEnergy (fun x y => κ (v x) (v y)) J := by
  classical
  unfold flowEnergy
  congr 1
  rw [sum_supported_image v hv
    (fun s => ∑ t, (embeddedCurrent v J s t) ^ 2 / κ s t) (by
      intro s hs
      simp only [embedded_current_off_image v J s _ (Or.inl hs),
        zero_pow (by decide : 2 ≠ 0), zero_div, Finset.sum_const_zero])]
  apply Finset.sum_congr rfl
  intro x _
  rw [sum_supported_image v hv
    (fun t => (embeddedCurrent v J (v x) t) ^ 2 / κ (v x) t) (by
      intro t ht
      rw [embedded_current_off_image v J (v x) t (Or.inr ht)]
      simp)]
  simp only [embedded_current_apply v hv J]

/-- INTERNAL: A finite leaf flow becomes a flow on the original state space,
with its pushed divergence and exactly the same energy.
TEXLINE: main.tex:670-683 -/
theorem embed_flow {α β : Type*} [Fintype α] [Fintype β] [DecidableEq β]
    (v : α → β) (hv : Function.Injective v) (κ : β → β → ℝ)
    (g : α → ℝ) (flow : FlowCertificate (fun x y => κ (v x) (v y)) g) :
    ∃ pushed : FlowCertificate κ (fun s => ∑ x, if v x = s then g x else 0),
      pushed.current = embeddedCurrent v flow.current ∧
      flowEnergy κ pushed.current = flowEnergy (fun x y => κ (v x) (v y)) flow.current := by
  classical
  have hsupport : ∀ s t, κ s t = 0 → embeddedCurrent v flow.current s t = 0 := by
    intro s t hz
    apply Finset.sum_eq_zero
    intro x _
    apply Finset.sum_eq_zero
    intro y _
    split_ifs with he
    · obtain ⟨rfl, rfl⟩ := he
      exact flow.supported x y hz
    · rfl
  have hdiv : ∀ s, divergence (embeddedCurrent v flow.current) s =
      ∑ x, if v x = s then g x else 0 := by
    intro s
    rw [embedded_current_divergence]
    simp only [flow.divergence_eq]
  exact ⟨⟨embeddedCurrent v flow.current,
    embedded_current_antisymmetric v flow.current flow.antisymmetric, hsupport, hdiv⟩,
    rfl, embedded_current_energy v hv κ flow.current⟩

end CountingMatroid.Analysis.EmbeddedFlow
