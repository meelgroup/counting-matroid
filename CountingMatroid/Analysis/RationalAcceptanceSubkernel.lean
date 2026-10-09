import CountingMatroid.Analysis.BoundedUniformSubkernel
import CountingMatroid.Analysis.SelectedMetropolisKernel
import CountingMatroid.Analysis.ChainDrawAbortAttribution

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! The exact numerator/denominator acceptance test is a finite-bit
subkernel of one rational Metropolis accept/reject decision. -/
namespace CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedMetropolisKernel

/-- INTERNAL: Value semantics of the program's final rational acceptance branch. -/
noncomputable def rationalAccept {α : Type} (tape : ℕ → Bool) (trials : ℕ) (ratio : ℚ)
    (state candidate : α) (start : ℕ) : Option (α × ℕ) :=
  if ratio < 1 then
    let draw := (boundedUniform tape trials ratio.den start).val
    draw.1.map (fun value =>
      (if value < ratio.num.natAbs then candidate else state, draw.2))
  else some (candidate, start)

/-- INTERNAL: The uniform numerator comparison has exactly the rational
acceptance mass, with its complementary mass returning to the source. -/
theorem rational_draw_average {α : Type} [DecidableEq α]
    (ratio : ℚ) (hr : 0 ≤ ratio) (hlt : ratio < 1) (state candidate next : α) :
    (1 / (ratio.den : ℝ)) * ∑ a : Fin ratio.den,
      (if (if a.val < ratio.num.natAbs then candidate else state) = next
        then (1 : ℝ) else 0) =
    exchangeOutcome state candidate next (ratio : ℝ) := by
  classical
  have hn : (ratio.num.natAbs : ℝ) = (ratio.num : ℝ) := by
    rw [Nat.cast_natAbs, abs_of_nonneg (by exact_mod_cast (Rat.num_nonneg.mpr hr))]
  have hratio : (ratio.num.natAbs : ℝ) / (ratio.den : ℝ) = (ratio : ℝ) := by
    rw [Rat.cast_def, hn]
  have hd : (0 : ℝ) < ratio.den := by exact_mod_cast ratio.den_pos
  have hnum : ratio.num.natAbs < ratio.den := by
    have h : (ratio.num.natAbs : ℝ) / (ratio.den : ℝ) < 1 := by
      rw [hratio]
      exact_mod_cast hlt
    exact_mod_cast (div_lt_one hd).mp h
  let cut : Fin ratio.den := ⟨ratio.num.natAbs, hnum⟩
  have hyes : Finset.univ.filter (fun a : Fin ratio.den => a.val < ratio.num.natAbs) =
      Finset.Iio cut := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Iio]
    rfl
  have hno : Finset.univ.filter (fun a : Fin ratio.den => ¬ a.val < ratio.num.natAbs) =
      Finset.Ici cut := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici, not_lt]
    rfl
  have hterm (a : Fin ratio.den) :
      (if (if a.val < ratio.num.natAbs then candidate else state) = next
        then (1 : ℝ) else 0) =
      if a.val < ratio.num.natAbs then (if candidate = next then 1 else 0)
      else (if state = next then 1 else 0) := by split_ifs <;> rfl
  simp_rw [hterm]
  rw [Finset.sum_ite, hyes, hno]
  simp only [Finset.sum_const, nsmul_eq_mul, Fin.card_Iio, Fin.card_Ici, cut]
  rw [Nat.cast_sub (by omega : ratio.num.natAbs ≤ ratio.den)]
  unfold exchangeOutcome
  rw [← hratio]
  field_simp
  <;> ring

/-- INTERNAL: Covered executions of the capped rational acceptance branch
are dominated by its exact Metropolis accept/reject distribution.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem rational_accept_covered_mass {α : Type} [DecidableEq α]
    (head : List Bool) (trials t : ℕ) (ratio : ℚ) (hr : 0 ≤ ratio)
    (state candidate next : α) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      rationalAccept tape trials ratio state candidate head.length = some (next, stop)) ≤
    exchangeOutcome state candidate next (min 1 (ratio : ℝ)) := by
  classical
  by_cases hlt : ratio < 1
  · have hmin : min 1 (ratio : ℝ) = (ratio : ℝ) := min_eq_right (by exact_mod_cast hlt.le)
    rw [hmin, ← rational_draw_average ratio hr hlt state candidate next]
    apply le_trans (fairMass_mono head t _
      (fun tape => ∃ (a : Fin ratio.den) (stop : ℕ), stop ≤ head.length + t ∧
        (boundedUniform tape trials ratio.den head.length).val = (some a.val, stop) ∧
        (if a.val < ratio.num.natAbs then candidate else state) = next) (by
      intro bits hs
      obtain ⟨stop, hstop, hrun⟩ := hs
      unfold rationalAccept at hrun
      rw [if_pos hlt] at hrun
      cases hd : (boundedUniform (finiteTape (head ++ bits.val))
          trials ratio.den head.length).val with
      | mk choice cursor =>
        cases choice with
        | none => simp [hd] at hrun
        | some value =>
          simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at hrun
          have hv := ObservationRoundDrawSites.boundedUniform_result_lt
            (finiteTape (head ++ bits.val)) trials ratio.den head.length value
            (by rw [hd])
          refine ⟨(⟨value, hv⟩ : Fin ratio.den), cursor, ?_, rfl, hrun.1⟩
          omega))
    apply bounded_uniform_bind_mass head trials ratio.den t ratio.den_pos
      (fun a _ _ => (if a.val < ratio.num.natAbs then candidate else state) = next)
      (fun a => if (if a.val < ratio.num.natAbs then candidate else state) = next
        then (1 : ℝ) else 0)
      (fun a => by split_ifs <;> positivity)
    intro a stop hlo hhi pref hdraw
    by_cases heq : (if a.val < ratio.num.natAbs then candidate else state) = next
    · rw [if_pos heq]
      exact fair_mass_le_one _ _ _
    · simp [fairMass, heq]
  · have hmin : min 1 (ratio : ℝ) = 1 := min_eq_left (by exact_mod_cast (not_lt.mp hlt))
    rw [hmin]
    simp only [exchangeOutcome, one_mul, sub_self, zero_mul, add_zero]
    have hevent (tape : ℕ → Bool) :
        (∃ stop, stop ≤ head.length + t ∧
          rationalAccept tape trials ratio state candidate head.length = some (next, stop)) ↔
        candidate = next := by
      simp [rationalAccept, hlt, Option.some.injEq, Prod.mk.injEq]
    simp only [fairMass, hevent]
    by_cases heq : candidate = next
    · simp [heq, card_vector]
    · simp [heq]

end CountingMatroid.Analysis.RationalAcceptanceSubkernel
