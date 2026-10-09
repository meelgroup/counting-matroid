import CountingMatroid.Analysis.SignatureOrthogonalNonpositive

set_option autoImplicit false

/-! The elementary determinant consequence of the two-pair Hessian signature. -/

namespace CountingMatroid.Analysis.TwoPairSignatureBound

open scoped Matrix

/-- INTERNAL: The two-pair Hessian, ordered by the retained pair variables.
TEXLINE: main.tex:408-412 -/
noncomputable def twoPairMatrix (a c z : ℚ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![2 * (a : ℝ), (z : ℝ); (z : ℝ), 2 * (c : ℝ)]

/-- PAPER: main.tex:408-412
A positive first diagonal and at most one positive direction force the
two-pair Hessian determinant to be nonpositive. -/
theorem two_pair_signature_bound (a c z : ℚ) (ha : 0 < a)
    (hsig : sigPos (twoPairMatrix a c z).toQuadraticForm' ≤ 1) :
    4 * c * a ≤ z ^ 2 := by
  have haR : 0 < (a : ℝ) := by exact_mod_cast ha
  let Q := (twoPairMatrix a c z).toQuadraticForm'
  have hcalc (u : Fin 2 → ℝ) :
      Q u = 2 * (a : ℝ) * u 0 ^ 2 +
        2 * (z : ℝ) * u 0 * u 1 + 2 * (c : ℝ) * u 1 ^ 2 := by
    dsimp [Q, twoPairMatrix, Matrix.toQuadraticForm']
    simp [Matrix.toLinearMap₂'_apply', dotProduct, Matrix.mulVec, Fin.sum_univ_succ]
    ring
  let e : Fin 2 → ℝ := ![1, 0]
  let v : Fin 2 → ℝ := ![-(z : ℝ), 2 * (a : ℝ)]
  have he : 0 < Q e := by rw [hcalc]; simp [e]; positivity
  have horth : Q.IsOrtho e v := by
    rw [QuadraticMap.isOrtho_def]
    simp only [hcalc]
    simp [e, v]
    ring
  have hv := SignatureOrthogonalNonpositive.signature_orthogonal_nonpositive
    Q hsig e v he (QuadraticMap.associated_isOrtho.mpr horth)
  rw [hcalc] at hv
  simp only [v, Matrix.cons_val_zero, Matrix.cons_val_one] at hv
  have hprod : (4 * (c : ℝ) * (a : ℝ) - (z : ℝ) ^ 2) * (2 * (a : ℝ)) ≤ 0 := by
    nlinarith [hv]
  have h : 4 * (c : ℝ) * (a : ℝ) ≤ (z : ℝ) ^ 2 :=
    sub_nonpos.mp (nonpos_of_mul_nonpos_left hprod (by positivity))
  exact_mod_cast h

end CountingMatroid.Analysis.TwoPairSignatureBound
