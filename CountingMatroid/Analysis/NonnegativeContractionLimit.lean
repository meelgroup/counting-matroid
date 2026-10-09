import CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
import CountingMatroid.Analysis.QuadraticHyperplanePointwiseLimit
import Mathlib.Topology.Instances.Rat
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

/-!
The boundary step for finite rationally weighted sums of real quadratic forms.
Strictly positive weights approximate nonnegative weights. Pointwise closure
of the nonpositive-hyperplane property gives the boundary case, without any
finite-dimensionality or tensor hypotheses.
-/

namespace CountingMatroid.Analysis.NonnegativeContractionLimit

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: Extend contraction closure from positive rational weights to
nonnegative rational weights, without any tensor or support hypotheses.
TEXLINE: main.tex:340-347 -/
theorem nonnegative_contraction_limit {σ V : Type} [Fintype σ]
    [AddCommGroup V] [Module ℝ V] [Invertible (2 : ℝ)]
    (Q : σ → QuadraticForm ℝ V)
    (hpositive : ∀ d : σ → ℚ, (∀ s, 0 < d s) →
      HasNonpositiveHyperplane (∑ s, (d s : ℝ) • Q s))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    HasNonpositiveHyperplane (∑ s, (d s : ℝ) • Q s) := by
  classical
  by_cases hstrict : ∀ s, 0 < d s
  · exact hpositive d hstrict
  let dn : ℕ → σ → ℚ := fun n s => d s + 1 / ((n : ℚ) + 1)
  have hdn (n : ℕ) (s : σ) : 0 < dn n s := by
    exact add_pos_of_nonneg_of_pos (hd s) (by positivity)
  let Qn : ℕ → QuadraticForm ℝ V := fun n => ∑ s, (dn n s : ℝ) • Q s
  have hn (n : ℕ) : HasNonpositiveHyperplane (Qn n) :=
    hpositive (dn n) (hdn n)
  have hcoeff (s : σ) : Filter.Tendsto (fun n => (dn n s : ℝ))
      Filter.atTop (nhds (d s : ℝ)) := by
    simpa [dn] using
      (tendsto_const_nhds (x := (d s : ℝ))).add
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hconv (v : V) : Filter.Tendsto (fun n => Qn n v) Filter.atTop
      (nhds ((∑ s, (d s : ℝ) • Q s) v)) := by
    simpa [Qn, sum_apply, smul_apply, smul_eq_mul] using
      tendsto_finsetSum Finset.univ (fun s _ => (hcoeff s).mul_const (Q s v))
  exact QuadraticHyperplanePointwiseLimit.has_nonpositive_hyperplane_of_pointwise_tendsto
    Qn (∑ s, (d s : ℝ) • Q s) hn hconv

end CountingMatroid.Analysis.NonnegativeContractionLimit

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · positive rational approximation and the proved associated-kernel pointwise closure lemma close the boundary case in arbitrary dimension.
* 2026-10-09 · decomposed · the strict-weight case closes directly; the associated-kernel limit route isolates closure at zero weights.
-/
