import CountingMatroid.Analysis.TransversalEventMean

set_option autoImplicit false

/-!
Signed exchange flows and their energy inequality. Conductances may vanish:
a flow must be zero on those pairs. These facts supply the summation-by-parts
and Cauchy--Schwarz step in the paper's transport construction; they do not
construct the recursively balanced flow or bound its energy.
-/

namespace CountingMatroid.Analysis.ExchangeFlowEnergy

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open Arlib.Probability
open scoped BigOperators

/-- INTERNAL: Net outgoing current of an antisymmetric finite flow.
TEXLINE: main.tex:493-510 -/
noncomputable def divergence {α : Type*} [Fintype α] (J : α → α → ℝ)
    (x : α) : ℝ := ∑ y, J x y

/-- INTERNAL: Energy of an antisymmetric current, counting each unoriented
edge once. Zero conductances are handled by the flow support condition.
TEXLINE: main.tex:502-510 -/
noncomputable def flowEnergy {α : Type*} [Fintype α]
    (κ J : α → α → ℝ) : ℝ := (1 / 2 : ℝ) * ∑ x, ∑ y, (J x y) ^ 2 / κ x y

/-- INTERNAL: Energy of a potential in the same unoriented-edge convention.
TEXLINE: main.tex:478-483 -/
noncomputable def potentialEnergy {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (H : α → ℝ) : ℝ :=
  (1 / 2 : ℝ) * ∑ x, ∑ y, κ x y * (H x - H y) ^ 2

/-- INTERNAL: Data needed from the paper's recursively balanced flow.
TEXLINE: main.tex:493-510,670-709 -/
structure FlowCertificate {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (demand : α → ℝ) where
  current : α → α → ℝ
  antisymmetric : ∀ x y, current x y = -current y x
  supported : ∀ x y, κ x y = 0 → current x y = 0
  divergence_eq : ∀ x, divergence current x = demand x

/-- PAPER: main.tex:499-507
Summation by parts turns a prescribed divergence into a pairing of edge
currents with potential differences. -/
theorem divergence_pairing {α : Type*} [Fintype α]
    (J : α → α → ℝ) (hJ : ∀ x y, J x y = -J y x) (H : α → ℝ) :
    (∑ x, divergence J x * H x) =
      (1 / 2 : ℝ) * ∑ x, ∑ y, J x y * (H x - H y) := by
  classical
  have hswap : (∑ x, ∑ y, J x y * H y) = -(∑ x, ∑ y, J x y * H x) := by
    rw [Finset.sum_comm]
    calc
      (∑ y, ∑ x, J x y * H y) = ∑ y, ∑ x, -(J y x * H y) := by
        apply Finset.sum_congr rfl
        intro y _
        apply Finset.sum_congr rfl
        intro x _
        rw [hJ x y, neg_mul]
      _ = _ := by simp only [Finset.sum_neg_distrib]
  simp only [divergence, Finset.sum_mul, mul_sub, Finset.sum_sub_distrib]
  rw [hswap]
  ring

/-- PAPER: main.tex:499-510
Cauchy--Schwarz bounds the squared divergence pairing by the current energy
times the potential energy, including pairs of zero conductance. -/
theorem flow_energy_bound {α : Type*} [Fintype α]
    (κ J : α → α → ℝ) (hκ : ∀ x y, 0 ≤ κ x y)
    (hJ : ∀ x y, J x y = -J y x)
    (hsupport : ∀ x y, κ x y = 0 → J x y = 0) (H : α → ℝ) :
    (∑ x, divergence J x * H x) ^ 2 ≤ flowEnergy κ J * potentialEnergy κ H := by
  classical
  have hcs := Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
    (s := (Finset.univ : Finset (α × α)))
    (r := fun xy => J xy.1 xy.2 * (H xy.1 - H xy.2))
    (f := fun xy => (J xy.1 xy.2) ^ 2 / κ xy.1 xy.2)
    (g := fun xy => κ xy.1 xy.2 * (H xy.1 - H xy.2) ^ 2)
    (fun xy _ => div_nonneg (sq_nonneg _) (hκ _ _))
    (fun xy _ => mul_nonneg (hκ _ _) (sq_nonneg _)) (by
      intro xy _
      by_cases hz : κ xy.1 xy.2 = 0
      · rw [hsupport _ _ hz, hz]
        simp
      · exact le_of_eq (by field_simp))
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Fintype.sum_prod_type] at hcs
  rw [divergence_pairing J hJ H]
  unfold flowEnergy potentialEnergy
  nlinarith [hcs]

/-- INTERNAL: The energy of a potential is nonnegative for nonnegative
conductances. -/
theorem potential_energy_nonneg {α : Type*} [Fintype α]
    (κ : α → α → ℝ) (hκ : ∀ x y, 0 ≤ κ x y) (H : α → ℝ) :
    0 ≤ potentialEnergy κ H := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (hκ x y) (sq_nonneg _)

/-- INTERNAL: A certified divergence and a current-energy bound suffice
for the corresponding potential-mean estimate.
TEXLINE: main.tex:499-510 -/
theorem FlowCertificate.pairing_sq_le {α : Type*} [Fintype α]
    {κ : α → α → ℝ} {demand : α → ℝ} (flow : FlowCertificate κ demand)
    (hκ : ∀ x y, 0 ≤ κ x y) (K : ℝ) (hcost : flowEnergy κ flow.current ≤ K)
    (H : α → ℝ) : (∑ x, demand x * H x) ^ 2 ≤ K * potentialEnergy κ H := by
  simp_rw [← flow.divergence_eq]
  exact (flow_energy_bound κ flow.current hκ flow.antisymmetric flow.supported H).trans
    (mul_le_mul_of_nonneg_right hcost (potential_energy_nonneg κ hκ H))

/-- INTERNAL: Unit source in a classifier fiber and unit sink in a finite
event, with the same totalized conditional denominators as the parent.
TEXLINE: main.tex:493-498,868-904 -/
noncomputable def conditionalMeanDemand {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) (A : Finset (PairedSet n)) (state : PairedSet n) : ℝ := by
  classical
  exact (if (classifyState state).val = kind then π state / classMass π kind else 0) -
    (if state ∈ A then π state / eventMass π A else 0)

/-- INTERNAL: The source-sink pairing is exactly the difference of the
conditional means used in the observable Poincare proof.
TEXLINE: main.tex:499-507,868-904 -/
theorem conditional_mean_demand_pairing {n : ℕ} (π : FinDist (PairedSet n))
    (kind : StateKind n) (A : Finset (PairedSet n)) (H : PairedSet n → ℝ) :
    (∑ state, conditionalMeanDemand π kind A state * H state) =
      classMean π H kind - eventMean π H A := by
  classical
  unfold conditionalMeanDemand classMean eventMean
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro state _
    split_ifs <;> simp [div_mul_eq_mul_div]
  · simp only [ite_mul, zero_mul]
    rw [Finset.sum_div]
    rw [← Finset.sum_filter]
    simp [div_mul_eq_mul_div]

end CountingMatroid.Analysis.ExchangeFlowEnergy
