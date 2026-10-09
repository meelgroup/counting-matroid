import CountingMatroid.Analysis.ConditionalSelectedStateSum
import CountingMatroid.Analysis.ConditionalOccupancyCoefficients
import CountingMatroid.Analysis.TwoPairSignatureBound
import CountingMatroid.Analysis.ThreePairSignatureSchur

set_option autoImplicit false

/-! The exact operational coefficients of the conditioned pair and triple
Hessians. ConditionalSelectedStateSum supplies normalization and the exact
state sums; ConditionalOccupancyCoefficients converts their occupancy tests
to operational defect and transversal totals and excludes cubic occupancy.
Finite matrix-entry enumeration preserves the derivative multiplicities.
This declaration supplies no signature premise. -/

namespace CountingMatroid.Analysis.ConditionalOperationalCoefficients

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalDefectQuadratics
open CountingMatroid.Analysis.ConditionalDefectExtractionCoefficients
open CountingMatroid.Analysis.ConditionalSelectedStateSum
open CountingMatroid.Analysis.ConditionalOccupancyCoefficients
open CountingMatroid.Analysis.TwoPairSignatureBound
open CountingMatroid.Analysis.ThreePairSignatureSchur

/-- PAPER: main.tex:403-417
After conditioning, exact exponent extraction gives the operational
transversal and ordered-defect entries of both Hessians. -/
theorem conditional_operational_coefficients (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (σ : Assignment n) :
      (∀ (i j : Fin n) (hij : i ≠ j), σ i = none → σ j = none →
        ∀ s t : Fin 2,
          (((conditionedPairPolynomial M₁ M₂ q σ).coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j] : Fin 2 → Fin n) + ordinaryExponent σ {i, j}) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          twoPairMatrix (defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩) (defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩) (transversalTotal r o₁ o₂ q σ) s t) ∧
      (∀ (i j k : Fin n) (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k),
        σ i = none → σ j = none → σ k = none → ∀ s t : Fin 3,
          (((conditionedPairPolynomial M₁ M₂ q σ).coeff ((Finsupp.single s 1 + Finsupp.single t 1).mapDomain
              (![i, j, k] : Fin 3 → Fin n) + Finsupp.single k 1 +
              ordinaryExponent σ {i, j, k}) *
            ((Finsupp.single s 1 + Finsupp.single t 1 : Fin 3 →₀ ℕ) 2 + 1) *
            (if s = t then 2 else 1) : ℚ) : ℝ) =
          threePairMatrix (defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩) (defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩)
            (defectTotal r o₁ o₂ q σ ⟨j, k, hjk⟩) (defectTotal r o₁ o₂ q σ ⟨i, k, hik⟩) (transversalTotal r o₁ o₂ q σ) s t) := by
  classical
  have hD (i j : Fin n) (hij : i ≠ j) (hi : σ i = none) (hj : σ j = none) :=
    operational_defect_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ
      ⟨i, j, hij⟩ hi hj
  have hT := operational_transversal_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ
  constructor
  · intro i j hij hi hj s t
    have hA : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 2 + ordinaryExponent σ {i, j}) =
        defectTotal r o₁ o₂ q σ ⟨j, i, hij.symm⟩ := by
      simpa only [Finset.pair_comm j i] using hD j i hij.symm hj hi
    have hC := hD i j hij hi hj
    have hZ : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 1 + Finsupp.single j 1 + ordinaryExponent σ {i, j}) =
        transversalTotal r o₁ o₂ q σ := by
      have he : Finsupp.single i 1 + Finsupp.single j 1 + ordinaryExponent σ {i, j} =
          ordinaryExponent σ ∅ := by
        ext x
        by_cases hxi : x = i <;> by_cases hxj : x = j <;>
          simp [ordinary_exponent_apply, hxi, hxj,
            hi, hj, hij, hij.symm]
      rw [he]
      exact hT
    fin_cases s <;> fin_cases t
    all_goals simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    · norm_num [twoPairMatrix, ← Finsupp.single_add, hA, mul_comm]
    · norm_num [twoPairMatrix, hZ]
    · norm_num [twoPairMatrix]
      rw [add_comm (Finsupp.single j 1) (Finsupp.single i 1)]
      exact hZ
    · norm_num [twoPairMatrix, ← Finsupp.single_add, hC, mul_comm]
  · intro i j k hij hjk hik hi hj hk s t
    have hD3 (a b c : Fin n) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
        (ha : σ a = none) (hb : σ b = none) (hc : σ c = none) :
        (conditionedPairPolynomial M₁ M₂ q σ).coeff
          (Finsupp.single a 1 + Finsupp.single a 1 + Finsupp.single c 1 +
            ordinaryExponent σ {a, b, c}) = defectTotal r o₁ o₂ q σ ⟨b, a, hab.symm⟩ := by
      have he : Finsupp.single a 1 + Finsupp.single a 1 + Finsupp.single c 1 +
          ordinaryExponent σ {a, b, c} =
          Finsupp.single a 2 + ordinaryExponent σ {b, a} := by
        ext x
        by_cases hxa : x = a <;> by_cases hxb : x = b <;> by_cases hxc : x = c <;>
          simp [ordinary_exponent_apply, hxa, hxb, hxc,
            ha, hb, hc, hab, hab.symm, hbc, hbc.symm, hac, hac.symm]
      rw [he]
      exact hD b a hab.symm hb ha
    have hA := hD3 i j k hij hjk hik hi hj hk
    have hC : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single j 1 + Finsupp.single j 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = defectTotal r o₁ o₂ q σ ⟨i, j, hij⟩ := by
      simpa only [Finset.insert_comm] using hD3 j i k hij.symm hik hjk hj hi hk
    have hDK : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 1 + Finsupp.single k 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = defectTotal r o₁ o₂ q σ ⟨j, k, hjk⟩ := by
      have hset : ({k, j, i} : Finset (Fin n)) = {i, j, k} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h := hD3 k j i hjk.symm hij.symm hik.symm hk hj hi
      rw [hset] at h
      simpa only [add_comm, add_left_comm, add_assoc] using h
    have hEK : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single j 1 + Finsupp.single k 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = defectTotal r o₁ o₂ q σ ⟨i, k, hik⟩ := by
      have hset : ({k, i, j} : Finset (Fin n)) = {i, j, k} := by
        ext x
        simp only [Finset.mem_insert, Finset.mem_singleton]
        tauto
      have h := hD3 k i j hik.symm hij hjk.symm hk hi hj
      rw [hset] at h
      simpa only [add_comm, add_left_comm, add_assoc] using h
    have hZ : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = transversalTotal r o₁ o₂ q σ := by
      have he : Finsupp.single i 1 + Finsupp.single j 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k} = ordinaryExponent σ ∅ := by
        ext x
        by_cases hxi : x = i <;> by_cases hxj : x = j <;> by_cases hxk : x = k <;>
          simp [ordinary_exponent_apply, hxi, hxj, hxk,
            hi, hj, hk, hij, hij.symm, hjk, hjk.symm, hik, hik.symm]
      rw [he]
      exact hT
    have hZero : (conditionedPairPolynomial M₁ M₂ q σ).coeff
        (Finsupp.single k 1 + Finsupp.single k 1 + Finsupp.single k 1 +
          ordinaryExponent σ {i, j, k}) = 0 := by
      apply operational_cubic_coefficient r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq σ _ k
      norm_num [Finsupp.single_apply, ordinary_exponent_apply]
    fin_cases s <;> fin_cases t
    all_goals simp only [Finsupp.mapDomain_add, Finsupp.mapDomain_single]
    all_goals norm_num [threePairMatrix, Finsupp.single_apply, Fin.ext_iff]
    · rw [hA]; ring
    · rw [hZ]
    · rw [hDK]; ring
    · rw [add_comm (Finsupp.single j 1) (Finsupp.single i 1), hZ]
    · rw [hC]; ring
    · rw [hEK]; ring
    · rw [add_comm (Finsupp.single k 1) (Finsupp.single i 1), hDK]; ring
    · rw [add_comm (Finsupp.single k 1) (Finsupp.single j 1), hEK]; ring
    · exact hZero

end CountingMatroid.Analysis.ConditionalOperationalCoefficients

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed all four pair and nine triple matrix entries using exact operational occupancy coefficients; preserved the statement and all prior imports.
* 2026-10-09 · decomposed · conditioned_state_coefficient replaces Tutte support preimages by operational PairedSet n sums. Finite matrix-case enumeration checks; remaining work is classification of the corresponding occupancy predicates and a transversal sum_bij. No normalization or rank-weight obligation remains here.
-/
