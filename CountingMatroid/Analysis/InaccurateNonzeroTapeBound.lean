import CountingMatroid.Interface.Pseudocode
import Mathlib.Data.Set.Finite.List
import CountingMatroid.Analysis.TransversalPartition
import CountingMatroid.Analysis.FiniteTapeProductAccuracy

set_option autoImplicit false

namespace CountingMatroid.Analysis.InaccurateNonzeroTapeBound

open CountingMatroid.Model

/-- INTERNAL: The product estimate and the final-parameter contamination
bound together imply the requested relative-error interval.
TEXLINE: main.tex:1305-1323 -/
private theorem inaccurate_product_contamination (ε z c y : ℚ)
    (hεpos : 0 < ε) (hεone : ε < 1) (hz : 0 ≤ z)
    (hcLower : z ≤ c) (hcUpper : c ≤ (1 + ε / 10) * z)
    (hyLower : (1 - ε / 4) * c ≤ y)
    (hyUpper : y ≤ (1 + ε / 4) * c) :
    (1 - ε) * z ≤ y ∧ y ≤ (1 + ε) * z := by
  constructor
  · have hfactor : 0 ≤ 1 - ε / 4 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcLower hfactor
    nlinarith
  · have hfactor : 0 ≤ 1 + ε / 4 := by linarith
    have hmul := mul_le_mul_of_nonneg_left hcUpper hfactor
    have hsmall : 0 ≤ ε * (1 - ε) * z := mul_nonneg (mul_nonneg (le_of_lt hεpos)
      (sub_nonneg.mpr (le_of_lt hεone))) hz
    nlinarith

/-- INTERNAL: At most one eighth of finite tapes complete with a nonzero
estimate outside the relative-error interval. This is the phase-estimation,
multiplier-induction, and product-accuracy part of the run analysis.
TEXLINE: main.tex:1253-1370 -/
theorem inaccurate_nonzero_tape_mass_bound (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
      y ≠ 0 ∧
        (y < (1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ) ∨
         (1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ) < y)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  dsimp only
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let z : ℚ := commonBaseCount M₁ M₂
  let answer : List Bool → ℚ := fun bits =>
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
      (fun i => (bits[i]?).getD false) s
  have hz : 0 ≤ z := by simp [z]
  let c : ℚ := TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ s.L)
  have hcontamination : z ≤ c ∧ c ≤ (1 + p.ε / 10) * z := by
    simpa only [z, c, s] using
      (TransversalPartition.transversal_partition_contamination
        n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂ hpositive)
  obtain ⟨hcLower, hcUpper⟩ := hcontamination
  have hmass :
      (Set.ncard {bits : List Bool | bits.length = m ∧
        answer bits ≠ 0 ∧
          (answer bits < (1 - p.ε / 4) * c ∨
           (1 + p.ε / 4) * c < answer bits)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
    simpa only [answer, c, s, m] using
      (FiniteTapeProductAccuracy.finite_tape_product_accuracy
        n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂ hpositive)
  let bad : Set (List Bool) := {bits | bits.length = m ∧
    answer bits ≠ 0 ∧
      (answer bits < (1 - p.ε) * z ∨
       (1 + p.ε) * z < answer bits)}
  let productBad : Set (List Bool) := {bits | bits.length = m ∧
    answer bits ≠ 0 ∧
      (answer bits < (1 - p.ε / 4) * c ∨
       (1 + p.ε / 4) * c < answer bits)}
  have hsubset : bad ⊆ productBad := by
    intro bits hb
    refine ⟨hb.1, hb.2.1, ?_⟩
    by_contra hnot
    have hwithin : (1 - p.ε / 4) * c ≤ answer bits ∧
        answer bits ≤ (1 + p.ε / 4) * c := by
      push Not at hnot
      exact hnot
    have haccurate := inaccurate_product_contamination p.ε z c (answer bits)
      p.ε_pos p.ε_lt_one hz hcLower hcUpper hwithin.1 hwithin.2
    rcases hb.2.2 with hl | hu
    · exact (not_lt_of_ge haccurate.1) hl
    · exact (not_lt_of_ge haccurate.2) hu
  have hfinite : productBad.Finite :=
    (List.finite_length_eq Bool m).subset (by intro bits hb; exact hb.1)
  have hcard : bad.ncard ≤ productBad.ncard :=
    Set.ncard_le_ncard hsubset hfinite
  calc
    (Set.ncard {bits : List Bool | bits.length = m ∧
      answer bits ≠ 0 ∧
        (answer bits < (1 - p.ε) * z ∨
         (1 + p.ε) * z < answer bits)} : ENNReal) *
        (1 / 2 : ENNReal) ^ m
      ≤ (productBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
          gcongr
    _ ≤ (1 / 8 : ENNReal) := by simpa [productBad] using hmass

end CountingMatroid.Analysis.InaccurateNonzeroTapeBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r8 · decomposed · the parent now elaborates from a concrete transversal partition sum; its contamination and finite-tape product estimates are separate open children. The live handoff request command was refused before execution.
* r7 · blocked · exact? and aesop leave the partition-sum/product-error witness; project search found no analytic partition sum, conditional phase law, or capped-draw coupling.
* r6 · decomposed · proved the deterministic product/contamination comparison and reduced the tape bound to a partition-sum witness with a narrower product-error event; its conditional phase estimate and finite-bit coupling remain open.
* r5 · open · direct simplification reduces the claim to a nonzero bad-tape count bound; phase estimates and product induction for `Program.boundedRun` are missing.
-/
