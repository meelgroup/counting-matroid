import CountingMatroid.Analysis.ExchangeFlowEnergy

set_option autoImplicit false

/-!
Summation of signed finite flows with disjoint used edges. Divergences add,
and edge disjointness makes the energy additive even at zero conductances.
-/

namespace CountingMatroid.Analysis.DisjointFlowSum

open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: Sum the currents indexed by a finite list of leaves.
TEXLINE: main.tex:681-709 -/
noncomputable def sumCurrent {ι α : Type*} (J : ι → α → α → ℝ) :
    List ι → α → α → ℝ
  | [], _, _ => 0
  | i :: rest, x, y => J i x y + sumCurrent J rest x y

/-- INTERNAL: Divergence commutes with a finite sum of currents.
TEXLINE: main.tex:684-709 -/
theorem sum_current_divergence {ι α : Type*} [Fintype α]
    (J : ι → α → α → ℝ) (leaves : List ι) (x : α) :
    divergence (sumCurrent J leaves) x =
      (leaves.map (fun i => divergence (J i) x)).sum := by
  induction leaves with
  | nil => simp [divergence, sumCurrent]
  | cons i rest ih =>
    simp only [divergence, sumCurrent, Finset.sum_add_distrib] at ih ⊢
    simp only [List.map_cons, List.sum_cons]
    rw [ih]

/-- INTERNAL: Multiplication by a current disjoint from every member
also annihilates their finite sum.
TEXLINE: main.tex:681-683 -/
private theorem mul_sum_current_zero {ι α : Type*} (J : ι → α → α → ℝ)
    (leaves : List ι) (a : ℝ) (x y : α)
    (hzero : ∀ i ∈ leaves, a * J i x y = 0) : a * sumCurrent J leaves x y = 0 := by
  induction leaves with
  | nil => simp [sumCurrent]
  | cons i rest ih =>
    rw [sumCurrent, mul_add, hzero i List.mem_cons_self,
      ih (fun j hj => hzero j (List.mem_cons_of_mem i hj)), zero_add]

/-- INTERNAL: Disjoint currents have additive unoriented energy.
TEXLINE: main.tex:681-683 -/
theorem disjoint_current_energy_add {α : Type*} [Fintype α]
    (κ J K : α → α → ℝ) (hdisjoint : ∀ x y, J x y * K x y = 0) :
    flowEnergy κ (fun x y => J x y + K x y) = flowEnergy κ J + flowEnergy κ K := by
  have hsq (x y : α) : (J x y + K x y) ^ 2 = (J x y) ^ 2 + (K x y) ^ 2 := by
    nlinarith [hdisjoint x y]
  simp only [flowEnergy, hsq, add_div, Finset.sum_add_distrib, mul_add]

/-- PAPER: main.tex:681-683
A sum of edge-disjoint leaf currents has exactly the sum of their energies. -/
theorem sum_current_energy {ι α : Type*} [Fintype α]
    (κ : α → α → ℝ) (J : ι → α → α → ℝ) (leaves : List ι)
    (hdisjoint : leaves.Pairwise (fun i j => ∀ x y, J i x y * J j x y = 0)) :
    flowEnergy κ (sumCurrent J leaves) =
      (leaves.map (fun i => flowEnergy κ (J i))).sum := by
  induction leaves with
  | nil => simp [flowEnergy, sumCurrent]
  | cons i rest ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hdisjoint
    have hc : ∀ x y, J i x y * sumCurrent J rest x y = 0 := by
      intro x y
      exact mul_sum_current_zero J rest (J i x y) x y (fun j hj => hhead j hj x y)
    change flowEnergy κ (fun x y => J i x y + sumCurrent J rest x y) = _
    rw [disjoint_current_energy_add κ (J i) (sumCurrent J rest) hc, ih htail]
    rfl

/-- INTERNAL: Summing supported antisymmetric currents produces a flow
certificate with summed divergence and, for disjoint edges, summed energy.
TEXLINE: main.tex:681-709 -/
theorem disjoint_flow_sum {ι α : Type*} [Fintype α]
    (κ : α → α → ℝ) (J : ι → α → α → ℝ) (d : ι → α → ℝ) (leaves : List ι)
    (hanti : ∀ i ∈ leaves, ∀ x y, J i x y = -J i y x)
    (hsupport : ∀ i ∈ leaves, ∀ x y, κ x y = 0 → J i x y = 0)
    (hdiv : ∀ i ∈ leaves, ∀ x, divergence (J i) x = d i x)
    (hdisjoint : leaves.Pairwise (fun i j => ∀ x y, J i x y * J j x y = 0)) :
    ∃ flow : FlowCertificate κ (fun x => (leaves.map (fun i => d i x)).sum),
      flow.current = sumCurrent J leaves ∧
      flowEnergy κ flow.current = (leaves.map (fun i => flowEnergy κ (J i))).sum := by
  have ha : ∀ x y, sumCurrent J leaves x y = -sumCurrent J leaves y x := by
    intro x y
    clear hsupport hdiv hdisjoint
    induction leaves with
    | nil => simp [sumCurrent]
    | cons i rest ih =>
      rw [sumCurrent, sumCurrent, hanti i List.mem_cons_self,
        ih (fun j hj => hanti j (List.mem_cons_of_mem i hj))]
      ring
  have hs : ∀ x y, κ x y = 0 → sumCurrent J leaves x y = 0 := by
    intro x y hz
    clear ha hanti hdiv hdisjoint
    induction leaves with
    | nil => rfl
    | cons i rest ih =>
      rw [sumCurrent, hsupport i List.mem_cons_self x y hz,
        ih (fun j hj => hsupport j (List.mem_cons_of_mem i hj)), zero_add]
  have hd : ∀ x, divergence (sumCurrent J leaves) x =
      (leaves.map (fun i => d i x)).sum := by
    intro x
    rw [sum_current_divergence]
    congr 1
    apply List.map_congr_left
    intro i hi
    exact hdiv i hi x
  exact ⟨⟨sumCurrent J leaves, ha, hs, hd⟩, rfl,
    sum_current_energy κ J leaves hdisjoint⟩

end CountingMatroid.Analysis.DisjointFlowSum
