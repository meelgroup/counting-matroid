import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.InitialRestartLaw
import CountingMatroid.Analysis.FiniteObservationMarkov

set_option autoImplicit false

namespace CountingMatroid.Analysis.ConditionalRestartAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: The concrete restart cap converts the paper's expected
transition budget into its stated Markov tail budget. This is arithmetic;
it does not assert an operational expectation or a fair-tape coupling.
TEXLINE: main.tex:1230-1239 -/
theorem restart_markov_budget (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    (20 * (n : ℚ) ^ 2 * (s.L : ℚ) * (s.τ : ℚ)) / (s.restartCap : ℚ) =
      (s.L : ℚ) / (100 * ((s.L : ℚ) + 1) ^ 2) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hτ : s.τ = 20 * n ^ 4 * (n * (s.L + 1) + 2) := by rfl
  have hcap : s.restartCap = 2000 * (s.L + 1) ^ 2 * n ^ 2 * s.τ := by rfl
  have hnq : (0 : ℚ) < n := by exact_mod_cast hn
  have hτpos : 0 < s.τ := by rw [hτ]; positivity
  have hτq : (0 : ℚ) < s.τ := by exact_mod_cast hτpos
  change _ / (s.restartCap : ℚ) = _
  rw [hcap]
  push_cast
  field_simp
  ring

/-- INTERNAL: Conditional finite-suffix mass of actual restart aborts. The
first term is the paper's restart-tail estimate; the second charges at most
three capped integer draws per permitted underlying transition.
TEXLINE: main.tex:1207-1239,1392-1421 -/
theorem conditional_restart_abort_mass (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
          s current.tables j current.bitCursor).val = none} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal (((s.L : ℚ) / (100 * ((s.L : ℚ) + 1) ^ 2) +
          3 * (s.restartCap : ℚ) * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
  classical
  dsimp only
  cases j with
  | zero =>
      have hempty : {suffix : List Bool |
          suffix.length = CountingMatroid.Model.Run.blockLength n r p - pref.length ∧
          (∀ a < 0, FirstPhaseFailure.CertifiedPhase r o₁ o₂
            (fun i => ((pref ++ suffix)[i]?).getD false)
            (CountingMatroid.Interface.Pseudocode.setup n p) a) ∧
          ∃ current : AnnealingCursor n,
            BoundedRunPhaseHistory.phaseHistory r o₁ o₂
              (fun i => ((pref ++ suffix)[i]?).getD false)
              (CountingMatroid.Interface.Pseudocode.setup n p) 0 = some current ∧
            (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
              (CountingMatroid.Interface.Pseudocode.setup n p) current.tables 0
              current.bitCursor).val = none} = ∅ := by
        ext suffix
        simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
        rintro ⟨_, _, current, hh, hs⟩
        have hc : BoundedRunPhaseHistory.initialCursor n
            (CountingMatroid.Interface.Pseudocode.setup n p) = current := Option.some.inj hh
        subst current
        rw [InitialRestartLaw.restartPhase_zero] at hs
        contradiction
      rw [hempty]
      simp
  | succ a =>
      rw [← restart_markov_budget n p hn]
      apply FiniteObservationMarkov.ennreal_mass_of_rat_bound
      -- BLOCKER: the remaining rational finite-suffix count must be bounded
      -- by 20*n²*L*τ/restartCap plus 3*restartCap*2^(-drawTrials).
      -- Unfolding restartPhase exposes nested capped traceReturn folds, but
      -- no uncapped return-excursion law or operational expected-cost bound
      -- connects them to Markov. The fair-suffix counting API and deterministic
      -- interval replay do not supply that estimate. Independently, the draw
      -- contribution needs the law of boundedUniform at adaptive positive
      -- denominators and sufficient remaining finite-block bits. Neither a
      -- generic hitting-time bound nor ENNReal coercion proves that coupling.
      -- A scratch `exact?` search on this normalized goal found no closing
      -- declaration; the operational moment and coupling are same-paper
      -- proof obligations, not candidates for an assumption in Prior.
      sorry

end CountingMatroid.Analysis.ConditionalRestartAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · reduced · proved `restart_markov_budget` from the actual schedule and used the existing rational-to-ENNReal mass bridge; `exact?` found no proof of the residual positive-phase suffix estimate. No new open helper.

* r24 · attempted · phase zero is empty by the proved fresh restart law; exposing positive-phase folds leaves the uncapped return-time expectation and capped-draw finite-suffix coupling.
-/
