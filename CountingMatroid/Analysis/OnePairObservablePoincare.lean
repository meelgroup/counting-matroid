import CountingMatroid.Analysis.ObservableProjection
import CountingMatroid.Analysis.ExchangeProposalGeometry

set_option autoImplicit false

/-!
The one-pair boundary case of observable Poincare. Only the two singleton
states may have positive mass. The ideal exchange proposal joins them with
probability one half, giving observable Poincare constant two for every law
supported on these states, without matroid or multiplier assumptions.
-/

namespace CountingMatroid.Analysis.OnePairObservablePoincare

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.ObservableProjection
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ExchangeProposalGeometry
open Arlib.Probability Arlib.Probability.FinDist

/-- INTERNAL: Enumerate the four subsets of one paired ground set.
TEXLINE: main.tex:244-293 -/
theorem one_pair_state_sum (f : PairedSet 1 → ℝ) :
    (∑ state, f state) =
      f ∅ + f {(0, false)} + f {(0, true)} + f {(0, false), (0, true)} := by
  classical
  have hU : (Finset.univ : Finset (PairedSet 1)) =
      {∅, {(0, false)}, {(0, true)}, {(0, false), (0, true)}} := by decide
  have h0 : (∅ : PairedSet 1) ∉
      ({{(0, false)}, {(0, true)}, {(0, false), (0, true)}} : Finset (PairedSet 1)) := by decide
  have hx : ({(0, false)} : PairedSet 1) ∉
      ({{(0, true)}, {(0, false), (0, true)}} : Finset (PairedSet 1)) := by decide
  have hy : ({(0, true)} : PairedSet 1) ∉
      ({{(0, false), (0, true)}} : Finset (PairedSet 1)) := by decide
  simp only [hU, Finset.sum_insert h0, Finset.sum_insert hx, Finset.sum_insert hy,
    Finset.sum_singleton]
  ring

/-- INTERNAL: On a one-pair ground set, zero mass on the rejected empty and
full states gives observable Poincare constant two.
TEXLINE: main.tex:926-951 -/
theorem one_pair_observable_poincare (π : FinDist (PairedSet 1))
    (hzero : π ∅ = 0) (hfull : π {(0, false), (0, true)} = 0)
    (H : PairedSet 1 → ℝ) :
    Var π (observableProjection π H) ≤
      2 * ((1 / 2 : ℝ) * ∑ state : PairedSet 1, ∑ next : PairedSet 1,
        exchangeProposal 1 (by decide) state next * min (π state) (π next) *
          (H state - H next) ^ 2) := by
  classical
  have hsum := π.sum_coe
  change (∑ state, π state) = 1 at hsum
  rw [one_pair_state_sum] at hsum
  rw [hzero, hfull] at hsum
  have hpY : π {(0, true)} = 1 - π {(0, false)} := by linarith
  have hclassX : (classifyState ({(0, false)} : PairedSet 1)).val = .transversal := by decide
  have hclassY : (classifyState ({(0, true)} : PairedSet 1)).val = .transversal := by decide
  have hvar : Var π (observableProjection π H) =
      π {(0, false)} * π {(0, true)} * (H {(0, false)} - H {(0, true)}) ^ 2 := by
    rw [Var_eq_ip_sub_sq]
    unfold ip Ex
    simp only [one_pair_state_sum, hzero, hfull, zero_mul, zero_add, add_zero,
      observableProjection, hclassX, hclassY]
    rw [hpY]
    ring
  have hc : ({(0, false)} : PairedSet 1)ᶜ = {(0, true)} := by decide
  have hxy : ({(0, false)} : PairedSet 1) ≠ {(0, true)} := by decide
  have hQxy : exchangeProposal 1 (by decide)
      ({(0, false)} : PairedSet 1) ({(0, true)} : PairedSet 1) = 1 / 2 := by
    have hav := exchange_proposal_average 1 (by decide) ({(0, false)} : PairedSet 1)
      (by decide) (fun next => if next = ({(0, true)} : PairedSet 1) then (1 : ℝ) else 0)
    simpa [hc, hxy, Finset.filter_singleton] using hav
  have hQyx : exchangeProposal 1 (by decide)
      ({(0, true)} : PairedSet 1) ({(0, false)} : PairedSet 1) = 1 / 2 := by
    rw [exchange_proposal_symmetric]
    exact hQxy
  have hmin0 (state : PairedSet 1) : min 0 (π state) = 0 :=
    min_eq_left (π.coe_nonneg state)
  have hmin0' (state : PairedSet 1) : min (π state) 0 = 0 :=
    min_eq_right (π.coe_nonneg state)
  have henergy : ((1 / 2 : ℝ) * ∑ state : PairedSet 1, ∑ next : PairedSet 1,
      exchangeProposal 1 (by decide) state next * min (π state) (π next) *
        (H state - H next) ^ 2) =
      (1 / 2 : ℝ) * min (π {(0, false)}) (π {(0, true)}) *
        (H {(0, false)} - H {(0, true)}) ^ 2 := by
    simp only [one_pair_state_sum, hzero, hfull, hmin0, hmin0',
      mul_zero, zero_mul, sub_self, zero_pow (by decide : 2 ≠ 0),
      zero_add, add_zero, hQxy, hQyx, min_comm]
    ring
  have hpX := π.coe_nonneg ({(0, false)} : PairedSet 1)
  have hpY0 := π.coe_nonneg ({(0, true)} : PairedSet 1)
  have hpX1 : π {(0, false)} ≤ 1 := by linarith
  have hpY1 : π {(0, true)} ≤ 1 := by linarith
  have hprod : π {(0, false)} * π {(0, true)} ≤
      min (π {(0, false)}) (π {(0, true)}) := by
    apply le_min
    · simpa only [mul_one] using mul_le_mul_of_nonneg_left hpY1 hpX
    · simpa only [one_mul] using mul_le_mul_of_nonneg_right hpX1 hpY0
  rw [hvar, henergy]
  have hbound := mul_le_mul_of_nonneg_right hprod
    (sq_nonneg (H {(0, false)} - H {(0, true)}))
  nlinarith [hbound]

end CountingMatroid.Analysis.OnePairObservablePoincare
