import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Tactic

set_option autoImplicit false

namespace CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: Multiplicative error of an empirical mean around its positive
stationary mean. TEXLINE: main.tex:1241-1255 -/
def RelativeEstimate (η mean estimate : ℚ) : Prop :=
  (1 - η) * mean ≤ estimate ∧ estimate ≤ (1 + η) * mean

/-- INTERNAL: Two positive means estimated with relative error at most η
have an empirical quotient within the paper's ratio interval. This is
arithmetic and assumes no independence of the observations.
TEXLINE: main.tex:1257-1270,1290-1304 -/
theorem relative_quotient_bounds (η a b x y : ℚ)
    (hη : 0 ≤ η) (hηlt : η < 1) (ha : 0 < a) (hb : 0 < b)
    (hx : RelativeEstimate η a x) (hy : RelativeEstimate η b y) :
    0 < x ∧ 0 < y ∧
      (1 - η) / (1 + η) ≤ (x / y) / (a / b) ∧
      (x / y) / (a / b) ≤ (1 + η) / (1 - η) := by
  have hm : 0 < 1 - η := sub_pos.mpr hηlt
  have hp : 0 < 1 + η := by linarith
  have hxp : 0 < x := (mul_pos hm ha).trans_le hx.1
  have hyp : 0 < y := (mul_pos hm hb).trans_le hy.1
  refine ⟨hxp, hyp, ?_, ?_⟩
  · apply (le_div_iff₀ (div_pos ha hb)).mpr
    have he : (1 - η) / (1 + η) * (a / b) =
        ((1 - η) * a) / ((1 + η) * b) := by
          rw [div_mul_div_comm]
    rw [he]
    exact div_le_div₀ hxp.le hx.1 hyp hy.2
  · apply (div_le_iff₀ (div_pos ha hb)).mpr
    have he : (1 + η) / (1 - η) * (a / b) =
        ((1 + η) * a) / ((1 - η) * b) := by
          rw [div_mul_div_comm]
    rw [he]
    exact div_le_div₀ (by positivity) hx.2 (mul_pos hm hb) hy.1

/-- PAPER: main.tex:1257-1270
Accurate empirical type means estimate the current ideal multiplier within
factor two. The factor-two drift then gives a factor-four good multiplier
at the next parameter. -/
theorem learned_multiplier_bounds (η w p₀ pᵢ x y ideal nextIdeal : ℚ)
    (hη : 0 ≤ η) (hηsmall : η ≤ 1 / 3)
    (hw : 0 < w) (hp₀ : 0 < p₀) (hpᵢ : 0 < pᵢ)
    (hx : RelativeEstimate η p₀ x) (hy : RelativeEstimate η pᵢ y)
    (hideal : w * p₀ / pᵢ = ideal)
    (hdrift : ideal / 2 ≤ nextIdeal ∧ nextIdeal ≤ 2 * ideal) :
    nextIdeal / 4 ≤ w * x / y ∧ w * x / y ≤ 4 * nextIdeal := by
  have hηlt : η < 1 := by linarith
  obtain ⟨hxp, hyp, hl, hu⟩ :=
    relative_quotient_bounds η p₀ pᵢ x y hη hηlt hp₀ hpᵢ hx hy
  have hidealpos : 0 < ideal := hideal ▸ div_pos (mul_pos hw hp₀) hpᵢ
  have hsame : (w * x / y) / ideal = (x / y) / (p₀ / pᵢ) := by
    rw [← hideal]
    field_simp
  rw [← hsame] at hl hu
  have hhalf : (1 / 2 : ℚ) ≤ (1 - η) / (1 + η) := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + η)).mpr
    linarith
  have htwo : (1 + η) / (1 - η) ≤ (2 : ℚ) := by
    apply (div_le_iff₀ (by linarith : 0 < 1 - η)).mpr
    linarith
  have hlo := (le_div_iff₀ hidealpos).mp (hhalf.trans hl)
  have hup := (div_le_iff₀ hidealpos).mp (hu.trans htwo)
  constructor <;> linarith [hdrift.1, hdrift.2]

end CountingMatroid.Analysis.RelativeObservationBounds
