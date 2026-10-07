import CountingMatroid.Analysis.OutputSupport
import CountingMatroid.Interface.ProgramModel
import CountingMatroid.Analysis.MedianAmplification

set_option autoImplicit false

namespace CountingMatroid.Analysis.OutputAccuracy

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: On a nonempty ground set, a negative pretest makes the charged
estimator return zero before drawing a tape.
TEXLINE: main.tex:283-289 -/
theorem estimate_zero_of_false (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (tape : ℕ → ℕ → Bool) (hne : n ≠ 0)
    (hf : (solver.run n r o₁ o₂).val = false) :
    (CountingMatroid.Program.estimate solver n r o₁ o₂ p tape).val = 0 := by
  simp [CountingMatroid.Program.estimate, CountingMatroid.Program.preprocess,
    CountingMatroid.Model.Operations.inputSizeIsZero, hne, hf]

/-- INTERNAL: On the empty ground, the unique subset is a basis of both
matroids, so the common-base count is one.
TEXLINE: main.tex:283 -/
theorem commonBaseCount_zeroGround (M₁ M₂ : Matroid (Fin 0)) :
    commonBaseCount M₁ M₂ = 1 := by
  classical
  obtain ⟨B₁, hB₁⟩ := M₁.exists_isBase
  obtain ⟨B₂, hB₂⟩ := M₂.exists_isBase
  have hB₁e : B₁ = ∅ := by ext i; exact Fin.elim0 i
  have hB₂e : B₂ = ∅ := by ext i; exact Fin.elim0 i
  subst B₁
  subst B₂
  have hs : (Finset.univ.filter (fun B : Finset (Fin 0) =>
      M₁.IsBase (B : Set (Fin 0)) ∧ M₂.IsBase (B : Set (Fin 0)))) = {∅} := by
    ext B
    have hBe : B = ∅ := by ext i; exact Fin.elim0 i
    subst B
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton, iff_true, Finset.coe_empty]
    exact ⟨hB₁, hB₂⟩
  change (Finset.univ.filter (fun B : Finset (Fin 0) =>
    M₁.IsBase (B : Set (Fin 0)) ∧ M₂.IsBase (B : Set (Fin 0)))).card = 1
  rw [hs]
  simp

/-- INTERNAL: A negative pretest places only zero answers in the charged
output law on a nonempty ground.
TEXLINE: main.tex:283-289, 1464-1469 -/
theorem output_zero_of_false (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (hne : n ≠ 0) (hf : (solver.run n r o₁ o₂).val = false) :
    ∀ x ∈ (Model.Run.outputLaw solver n r o₁ o₂ p).support, x.1 = 0 := by
  intro x hx
  obtain ⟨run, hrun, heq⟩ :=
    (OutputSupport.outputLaw_support_iff solver n r o₁ o₂ p x).mp hx
  obtain ⟨blocks, _, hblocks⟩ :=
    (OutputSupport.algorithmLaw_support_iff solver n r o₁ o₂ p run).mp hrun
  have hz : run.val = 0 := by
    rw [← hblocks]
    exact estimate_zero_of_false solver n r o₁ o₂ p
      (Model.Run.blockTape blocks) hne hf
  simpa [← heq] using hz

/-- PAPER: main.tex:1253-1329, 1442-1470
The annealing estimate and median amplification meet the relative-error law;
the pretest handles the zero case exactly. -/
theorem output_accuracy (solver : FeasibilityImplementation)
    (hcorrect : FeasibilityCorrect solver) :
    ∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
      (o₁ o₂ : IndependenceOracle n) (p : InputParams),
      FullGround M₁ M₂ → CommonRank r M₁ M₂ →
      ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
      let law := Model.Run.outputLaw solver n r o₁ o₂ p
      let Z : ℚ := commonBaseCount M₁ M₂
      law.toOuterMeasure
        {x | x.1 < (1 - p.ε) * Z ∨ (1 + p.ε) * Z < x.1} ≤
          ENNReal.ofReal (p.δ : ℝ) ∧
      (Z = 0 → ∀ x ∈ law.support, x.1 = 0) := by
  intro n r M₁ M₂ o₁ o₂ p hfull hr h₁ h₂
  have htest := hcorrect n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
  refine ⟨?_, ?_⟩
  · have hpure :
        (CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p).toOuterMeasure
          {y : ℚ | y < (1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ) ∨
            (1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ) < y} ≤
          ENNReal.ofReal (p.δ : ℝ) := by
      by_cases hne : n = 0
      · subst n
        have hcount := commonBaseCount_zeroGround M₁ M₂
        have hconst :
            CountingMatroid.Interface.Pseudocode.estimateLaw solver 0 r o₁ o₂ p =
              PMF.pure (1 : ℚ) := by
          simp [CountingMatroid.Interface.Pseudocode.estimateLaw,
            CountingMatroid.Interface.Pseudocode.estimate,
            CountingMatroid.Interface.Pseudocode.pretest,
            CountingMatroid.Program.preprocess,
            CountingMatroid.Model.Operations.inputSizeIsZero]
          change PMF.map (Function.const (List (List Bool)) (1 : ℚ)) _ = _
          exact PMF.map_const _ _
        rw [hconst, hcount]
        simp only [PMF.toOuterMeasure_pure_apply, Set.mem_setOf_eq]
        split_ifs with hbad
        · rcases hbad with hbad | hbad <;>
            simp only [Nat.cast_one, mul_one] at hbad <;> nlinarith [p.ε_pos]
        · exact bot_le
      · by_cases hz : commonBaseCount M₁ M₂ = 0
        · have hf : (solver.run n r o₁ o₂).val = false := by
            simpa [hz] using htest
          have hconst :
              CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p =
                PMF.pure (0 : ℚ) := by
            simp [CountingMatroid.Interface.Pseudocode.estimateLaw,
              CountingMatroid.Interface.Pseudocode.estimate,
              CountingMatroid.Interface.Pseudocode.pretest,
              CountingMatroid.Program.preprocess,
              CountingMatroid.Model.Operations.inputSizeIsZero, hne, hf]
            change PMF.map (Function.const (List (List Bool)) (0 : ℚ)) _ = _
            exact PMF.map_const _ _
          rw [hconst, hz]
          simp [PMF.toOuterMeasure_pure_apply]
        have hpositive : 0 < commonBaseCount M₁ M₂ := Nat.pos_of_ne_zero hz
        have hf : (solver.run n r o₁ o₂).val = true := by
          simpa [hpositive] using htest
        have hpretest :
            CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ = none := by
          simp [CountingMatroid.Interface.Pseudocode.pretest,
            CountingMatroid.Program.preprocess,
            CountingMatroid.Model.Operations.inputSizeIsZero, hne, hf]
        exact MedianAmplification.median_amplification_bound solver n r o₁ o₂ p
          ((1 - p.ε) * (commonBaseCount M₁ M₂ : ℚ))
          ((1 + p.ε) * (commonBaseCount M₁ M₂ : ℚ)) hpretest
          (SingleRunAccuracy.single_run_accuracy_bound n r M₁ M₂ o₁ o₂ p
            hfull hr h₁ h₂ hpositive)
    rw [← CountingMatroid.outputLaw_answer_eq solver n r o₁ o₂ p] at hpure
    simpa only [PMF.toOuterMeasure_map_apply, Set.preimage_setOf_eq] using hpure
  · intro hZ
    have hZnat : commonBaseCount M₁ M₂ = 0 := by exact_mod_cast hZ
    have hne : n ≠ 0 := by
      intro hn
      subst n
      have hcount := commonBaseCount_zeroGround M₁ M₂
      omega
    have hf : (solver.run n r o₁ o₂).val = false := by
      simpa [hZnat] using htest
    exact output_zero_of_false solver n r o₁ o₂ p hne hf

end CountingMatroid.Analysis.OutputAccuracy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · parallel handoff · reduced the positive-input bound to `single_run_accuracy_bound` and `median_amplification_bound`; proved empty and infeasible cases and transferred the charged output law.
* r1 · open · proved exact zero output through the pretest and support lemmas; the positive-count probability estimate remains open.
-/
