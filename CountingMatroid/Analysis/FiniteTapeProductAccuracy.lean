import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List
import CountingMatroid.Analysis.RatioProductAccuracy
import CountingMatroid.Analysis.FiniteTapePhaseControl

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapeProductAccuracy

open CountingMatroid.Model

/-- INTERNAL: At most one eighth of capped finite tapes yield a completed
product farther than ε/4 from the concrete final transversal partition sum.
The deterministic product implication is proved in `RatioProductAccuracy`;
the remaining phase probability and finite-tape coupling obligation is
`FiniteTapePhaseControl.finite_tape_inaccurate_ratios`.
TEXLINE: main.tex:1207-1315,1392-1421 -/
theorem finite_tape_product_accuracy (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let c := CountingMatroid.Analysis.TransversalPartition.partitionSum
      r o₁ o₂ (s.ρ ^ s.L)
    (Set.ncard {bits : List Bool | bits.length = m ∧
      let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
      y ≠ 0 ∧
        (y < (1 - p.ε / 4) * c ∨
         (1 + p.ε / 4) * c < y)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  by_cases hn : n = 0
  · subst n
    have hL : (CountingMatroid.Interface.Pseudocode.setup 0 p).L = 0 := by
      unfold CountingMatroid.Interface.Pseudocode.setup CountingMatroid.Program.schedule
      simp only [Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_pure, CountingMatroid.Model.Operations.natMul,
        CountingMatroid.Model.Operations.natAdd,
        CountingMatroid.Model.Operations.ratDiv,
        Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany]
      simp
    have hrun (bits : List Bool) :
        CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false)
          (CountingMatroid.Interface.Pseudocode.setup 0 p) = (1 : ℚ) := by
      simp [CountingMatroid.Interface.Pseudocode.singleRun,
        CountingMatroid.Program.boundedRun, hL,
        CountingMatroid.Program.natPower,
        CountingMatroid.Model.Operations.ratMul,
        CountingMatroid.Model.Operations.ratOfNat,
        Arlib.Computation.Charged.repeatFor]
    have hc : CountingMatroid.Analysis.TransversalPartition.partitionSum
        r o₁ o₂ ((CountingMatroid.Interface.Pseudocode.setup 0 p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup 0 p).L) = 1 := by
      simp [CountingMatroid.Analysis.TransversalPartition.partitionSum,
        CountingMatroid.Analysis.TransversalPartition.transversalDeficiency,
        CountingMatroid.Analysis.TransversalPartition.transversalState]
    have hempty : {bits : List Bool |
        bits.length = CountingMatroid.Model.Run.blockLength 0 r p ∧
        let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false)
          (CountingMatroid.Interface.Pseudocode.setup 0 p)
        y ≠ 0 ∧
          (y < (1 - p.ε / 4) * 1 ∨ (1 + p.ε / 4) * 1 < y)} = ∅ := by
      ext bits
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rw [hrun] at h
      rcases h.2.2 with hbad | hbad <;> nlinarith [p.ε_pos]
    simp only [hc, hempty, Set.ncard_empty, Nat.cast_zero, zero_mul]
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
    let answer := fun bits : List Bool =>
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
    have hρ : 0 < s.ρ := by
      change 0 < 1 - 1 / ((2 * n : ℕ) : ℚ)
      push_cast
      have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hnpos
      apply sub_pos.mpr
      apply (div_lt_one (by positivity : (0 : ℚ) < 2 * n)).mpr
      linarith
    have hη : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
      change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
      push_cast
      rfl
    have hC : ∀ j, 0 < C j := by
      intro j
      apply Finset.sum_pos
      · intro A _
        exact pow_pos (pow_pos hρ j) _
      · exact Finset.univ_nonempty
    have hCzero : C 0 = (2 : ℚ) ^ n := by
      simp [C, TransversalPartition.partitionSum]
    have hgood (bits : List Bool)
        (h : FiniteTapePhaseControl.AccurateRatioProduct n r o₁ o₂ p
          (fun i => (bits[i]?).getD false)) :
        (1 - p.ε / 4) * C s.L ≤ answer bits ∧
          answer bits ≤ (1 + p.ε / 4) * C s.L := by
      obtain ⟨R, hout, hR⟩ := h
      have hratios : ∀ j < s.L,
          (1 - p.ε / (32 * ((s.L : ℚ) + 1))) /
            (1 + p.ε / (32 * ((s.L : ℚ) + 1))) ≤ R j / (C (j + 1) / C j) ∧
          R j / (C (j + 1) / C j) ≤
            (1 + p.ε / (32 * ((s.L : ℚ) + 1))) /
              (1 - p.ε / (32 * ((s.L : ℚ) + 1))) := by
        simpa only [← hη] using hR
      have hp := RatioProductAccuracy.ratio_product_accuracy s.L p.ε C R
        p.ε_pos p.ε_lt_one hC hratios
      rw [hCzero] at hp
      simpa only [answer, s, hout] using hp
    let bad : Set (List Bool) := {bits | bits.length = m ∧
      answer bits ≠ 0 ∧ (answer bits < (1 - p.ε / 4) * C s.L ∨
        (1 + p.ε / 4) * C s.L < answer bits)}
    let phaseBad : Set (List Bool) := {bits | bits.length = m ∧
      answer bits ≠ 0 ∧ ¬ FiniteTapePhaseControl.AccurateRatioProduct
        n r o₁ o₂ p (fun i => (bits[i]?).getD false)}
    have hsubset : bad ⊆ phaseBad := by
      intro bits hb
      refine ⟨hb.1, hb.2.1, ?_⟩
      intro hg
      have haccurate := hgood bits hg
      rcases hb.2.2 with hl | hu
      · exact (not_lt_of_ge haccurate.1) hl
      · exact (not_lt_of_ge haccurate.2) hu
    have hfinite : phaseBad.Finite :=
      (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
    have hcard : bad.ncard ≤ phaseBad.ncard := Set.ncard_le_ncard hsubset hfinite
    change (bad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤ _
    calc
      (bad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
          (phaseBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
        gcongr
      _ ≤ (1 / 8 : ENNReal) :=
        FiniteTapePhaseControl.finite_tape_inaccurate_ratios
          n r M₁ M₂ o₁ o₂ p hnpos hfull hr h₁ h₂ hpositive

end CountingMatroid.Analysis.FiniteTapeProductAccuracy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · blocked · the parent elaborates, but the phase-control child remains open after mechanical handoff rejection; this is a checked reduction with retained proof debt, not an outright closure.
* r16 · decomposed · proved the deterministic ratio-product estimate and the bad-event inclusion; the parent now uses the separate accurate-ratio witness probability obligation in `FiniteTapePhaseControl`.
* r15 · blocked · direct `exact?` and unfolding `singleRun` followed by `aesop` leave the positive-ground event bound; identified the missing joint rejection-draw value/cursor law and the downstream-only finite-tape counting conversion. No proof debt was moved or closed.
* r14 · recovery diagnosis · isolated the needed proof-side phase transcript, transition-law identity, conditional phase estimate, and bounded-run/finite-block coupling; no existing declaration supplies the first bridge, so the positive-ground theorem remains open.
* r13 · blocked · `exact?` and `aesop` leave the positive-ground count inequality; `chainStepLaw` is only a finite-tape PMF, and the project has no paired-state ideal-chain law or conditional phase estimate to connect it to the paper's Markov/MSE argument.
* r12 · blocked · positive-ground `exact?` and `aesop` leave the same event-mass inequality; Arlib has generic Markov/Chebyshev and Metropolis results, but no distributional bridge from `chainStep`, conditional phase law, or uncapped-to-capped coupling.
* r11 · blocked · `aesop` leaves the positive-ground event-mass inequality and `exact?` finds no matching theorem. Mathlib has Chebyshev, but the program has no finite-tape phase law, mean-square bound, or uncapped-to-capped coupling to which it applies.
* r10 · blocked · `exact?` cannot close the positive-ground event bound; source search found no finite-chain trace/MSE analysis, good-multiplier invariant, or uncapped-to-`boundedRun` coupling. The paper proves these steps at main.tex:1207-1315, so this is a same-paper dependency, not a Prior proposal.
* r9 · partial · proved the empty-ground event is empty; positive-ground `aesop` leaves the event-mass inequality, with conditional phase bounds and capped finite-tape coupling absent.
* r8 · open · `aesop` leaves the finite-tape product-event bound; no conditional phase law or uncapped-to-capped coupling is formalized.
-/
