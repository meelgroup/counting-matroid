import CountingMatroid.Analysis.QuadraticNonpositiveHyperplane
import Mathlib.Combinatorics.Matroid.Rank.ENat
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Data.Fintype.Powerset

set_option autoImplicit false

/-!
The two-element rank-weight signature calculation. Submodularity bounds the
pair coefficient by the product of the singleton coefficients. The resulting
quadratic has a nonpositive hyperplane, as seen by completing two squares.
-/

namespace CountingMatroid.Analysis.BinaryRankWeightSignature

open QuadraticNonpositiveHyperplane
open scoped BigOperators

/-- INTERNAL: The elementary quadratic rank-weight form has a nonpositive
hyperplane whenever its mixed coefficient lies between zero and the product
of its singleton coefficients.
TEXLINE: main.tex:334-348 -/
theorem binary_form_nonpositive_hyperplane {V : Type} [AddCommGroup V] [Module ℝ V]
    (z x y : V →ₗ[ℝ] ℝ) (b c d : ℝ) (hb : 0 < b) (hc : 0 < c)
    (hd : 0 ≤ d) (hbc : d ≤ b * c) :
    HasNonpositiveHyperplane
      ((2 : ℝ) • QuadraticMap.linMulLin z z + (2 * b) • QuadraticMap.linMulLin z x +
        (2 * c) • QuadraticMap.linMulLin z y + (2 * d) • QuadraticMap.linMulLin x y) := by
  refine ⟨(2 : ℝ) • z + b • x + c • y, ?_⟩
  intro v hv
  simp only [LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at hv
  have hz : z v = -(b * x v + c * y v) / 2 := by linarith
  have hneg : 0 ≤ (b * c - d) * (b * x v + c * y v) ^ 2 +
      d * (b * x v - c * y v) ^ 2 :=
    add_nonneg (mul_nonneg (sub_nonneg.mpr hbc) (sq_nonneg _))
      (mul_nonneg hd (sq_nonneg _))
  have hidentity : 2 * b * c *
      (2 * (z v * z v) + (2 * b) * (z v * x v) +
        (2 * c) * (z v * y v) + (2 * d) * (x v * y v)) =
      -((b * c - d) * (b * x v + c * y v) ^ 2 +
        d * (b * x v - c * y v) ^ 2) := by
    rw [hz]
    ring
  have hscale : 0 < 2 * b * c := by positivity
  simp only [QuadraticMap.add_apply, QuadraticMap.smul_apply,
    QuadraticMap.linMulLin_apply, smul_eq_mul]
  apply (mul_le_mul_iff_left₀ hscale).mp
  rw [zero_mul, mul_comm, hidentity]
  exact neg_nonpos.mpr hneg

/-- INTERNAL: Matroid rank submodularity gives the precise coefficient
inequality used in the two-element quadratic calculation.
TEXLINE: main.tex:334-348 -/
theorem rank_weight_pair_le {α : Type} [Finite α] (N : Matroid α)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1) (s t : α) :
    (q ^ (N.eRk ({s, t} : Set α)).toNat)⁻¹ ≤
      (q ^ (N.eRk ({s} : Set α)).toNat)⁻¹ *
        (q ^ (N.eRk ({t} : Set α)).toNat)⁻¹ := by
  have hr := N.eRk_union_le_eRk_add_eRk ({s} : Set α) ({t} : Set α)
  have hs := (N.isRkFinite_set ({s} : Set α)).eRk_lt_top.ne
  have ht := (N.isRkFinite_set ({t} : Set α)).eRk_lt_top.ne
  have hn := ENat.toNat_le_toNat hr (by simp [hs, ht])
  rw [ENat.toNat_add hs ht] at hn
  have hp : q ^ ((N.eRk ({s} : Set α)).toNat + (N.eRk ({t} : Set α)).toNat) ≤
      q ^ (N.eRk ({s, t} : Set α)).toNat := by
    apply pow_le_pow_of_le_one hq.le hqone
    simpa only [Set.singleton_union] using hn
  rw [← mul_inv_rev, ← pow_add]
  exact (inv_le_inv₀ (pow_pos hq _) (pow_pos hq _)).mpr (by simpa only [Nat.add_comm] using hp)

/-- INTERNAL: The original-variable quadratic signature invariant is proved
for every matroid on two elements, directly from rank submodularity.
TEXLINE: main.tex:334-348 -/
theorem binary_tutte_nonpositive_hyperplane {α : Type} [Fintype α] [DecidableEq α]
    (N : Matroid α) (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (htwo : Fintype.card α = 2) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) : ℚ) : ℝ))) := by
  classical
  dsimp only
  obtain ⟨s, t, hst, hu⟩ := Finset.card_eq_two.mp
    (show (Finset.univ : Finset α).card = 2 by simpa)
  let b : ℚ := (q ^ (N.eRk ({s} : Set α)).toNat)⁻¹
  let c : ℚ := (q ^ (N.eRk ({t} : Set α)).toNat)⁻¹
  let d : ℚ := (q ^ (N.eRk ({s,t} : Set α)).toNat)⁻¹
  have hsets : (Finset.univ : Finset (Finset α)) = {∅, {s}, {t}, {s,t}} := by
    rw [← Finset.powerset_univ, hu]
    simp [Finset.powerset_insert]
    ext A
    simp [or_left_comm, or_assoc, eq_comm]
  have hstsets : ({s} : Finset α) ≠ {t} := by simpa using hst
  have hs_pair : ({s} : Finset α) ≠ {s,t} := by
    intro h
    have ht : t ∈ ({s} : Finset α) := h.symm ▸ (by simp)
    exact hst (Finset.mem_singleton.mp ht).symm
  have ht_pair : ({t} : Finset α) ≠ {s,t} := by
    intro h
    have hs : s ∈ ({t} : Finset α) := h.symm ▸ (by simp)
    exact hst (Finset.mem_singleton.mp hs)
  have hempair : (∅ : Finset α) ≠ {s,t} := by
    intro h
    have hs : s ∈ (∅ : Finset α) := h.symm ▸ (by simp)
    simp at hs
  have hT : (∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a) : MvPolynomial (Option α) ℚ) =
      MvPolynomial.X none ^ 2 +
        MvPolynomial.C b * MvPolynomial.X none * MvPolynomial.X (some s) +
        MvPolynomial.C c * MvPolynomial.X none * MvPolynomial.X (some t) +
        MvPolynomial.C d * MvPolynomial.X (some s) * MvPolynomial.X (some t) := by
    rw [hsets]
    rw [Finset.sum_insert (by simp [hempair]),
      Finset.sum_insert (by simp [hstsets, hs_pair]),
      Finset.sum_insert (by simp [ht_pair]), Finset.sum_singleton]
    simp [htwo, hst, Finset.prod_insert, b, c, d]
    ring
  rw [hT]
  have hoption : (Finset.univ : Finset (Option α)) = {none, some s, some t} := by
    ext x
    cases x with
    | none => simp
    | some x =>
      have hx : x ∈ ({s,t} : Finset α) := hu ▸ Finset.mem_univ x
      simpa using hx
  let H : Matrix (Option α) (Option α) ℝ := fun i j => ((MvPolynomial.constantCoeff
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j
          (MvPolynomial.X none ^ 2 +
            MvPolynomial.C b * MvPolynomial.X none * MvPolynomial.X (some s) +
            MvPolynomial.C c * MvPolynomial.X none * MvPolynomial.X (some t) +
            MvPolynomial.C d * MvPolynomial.X (some s) * MvPolynomial.X (some t)))) : ℚ) : ℝ)
  have htwoCoeff : MvPolynomial.constantCoeff (2 : MvPolynomial (Option α) ℚ) = 2 :=
    map_ofNat _ _
  have hform : H.toQuadraticForm' =
      (2 : ℝ) • QuadraticMap.linMulLin (LinearMap.proj none) (LinearMap.proj none) +
        (2 * (b : ℝ)) • QuadraticMap.linMulLin (LinearMap.proj none) (LinearMap.proj (some s)) +
        (2 * (c : ℝ)) • QuadraticMap.linMulLin (LinearMap.proj none) (LinearMap.proj (some t)) +
        (2 * (d : ℝ)) • QuadraticMap.linMulLin (LinearMap.proj (some s)) (LinearMap.proj (some t)) := by
    ext v
    simp only [Matrix.toQuadraticForm', LinearMap.BilinMap.toQuadraticMap_apply,
      Matrix.toLinearMap₂'_apply]
    rw [hoption]
    simp [H, MvPolynomial.pderiv_X, Pi.single_apply, hst, hst.symm,
      QuadraticMap.linMulLin_apply, htwoCoeff]
    ring
  change HasNonpositiveHyperplane H.toQuadraticForm'
  rw [hform]
  apply binary_form_nonpositive_hyperplane
  · exact_mod_cast inv_pos.mpr (pow_pos hq _)
  · exact_mod_cast inv_pos.mpr (pow_pos hq _)
  · exact_mod_cast (inv_pos.mpr (pow_pos hq _)).le
  · exact_mod_cast rank_weight_pair_le N q hq hqone s t

end CountingMatroid.Analysis.BinaryRankWeightSignature
