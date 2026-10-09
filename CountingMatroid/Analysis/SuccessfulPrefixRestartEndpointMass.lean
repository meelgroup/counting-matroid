import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.RestartPhaseTransversal

set_option autoImplicit false

/-!
The finite-suffix restart endpoint sublaw needed for recorded-path domination.
Successful restarts contribute their returned state; aborted restarts contribute
zero. The warm endpoint comparison remains an operational proof obligation.
-/
namespace CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Marginal state mass of the actual capped restart, retaining
its adaptive bit cursor and the original defaulted finite tape.
TEXLINE: main.tex:1163-1176,1207-1244,1392-1421 -/
noncomputable def restartSuffixMass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ)
    (state : PairedSet n) : ℝ := by
  classical
  exact ∑ suffix : List.Vector Bool t,
    if ((restartPhase r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false)
      s current.tables j current.bitCursor).val).map Prod.fst = some state
    then 1 / (2 : ℝ) ^ t else 0

/-- INTERNAL: Transfer the paper's uncapped warm restart endpoint bound to
the actual capped finite-suffix sublaw. This excludes aborts, without
renormalising the successful restart distribution.
TEXLINE: main.tex:1207-1244,1392-1421 -/
theorem successful_prefix_restart_endpoint_mass_domination (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (current : AnnealingCursor n) (hw : ∀ a, 0 < current.currentWeights a)
    (hgood : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
      (CountingMatroid.Interface.Pseudocode.setup n p) j current)
    (hfixed : ∀ suffix : List.Vector Bool
        (CountingMatroid.Model.Run.blockLength n r p - pref.length),
      BoundedRunPhaseHistory.phaseHistory r o₁ o₂
        (fun i => ((pref ++ suffix.val)[i]?).getD false)
        (CountingMatroid.Interface.Pseudocode.setup n p) j = some current)
    (state : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let hq := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 j
    restartSuffixMass r o₁ o₂ s j current pref t state ≤
      (10 * (n : ℝ) ^ 2) *
        IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ j)
          current.currentWeights hq hw state := by
  classical
  dsimp only
  by_cases hinvalid : (classifyState state).val ≠ .transversal
  · have hzero : restartSuffixMass r o₁ o₂
        (CountingMatroid.Interface.Pseudocode.setup n p) j current pref
        (CountingMatroid.Model.Run.blockLength n r p - pref.length) state = 0 := by
      unfold restartSuffixMass
      apply Finset.sum_eq_zero
      intro suffix _
      apply if_neg
      intro hstate
      obtain ⟨start, hstart, heq⟩ := Option.map_eq_some_iff.mp hstate
      change start.1 = state at heq
      exact hinvalid (heq ▸ RestartPhaseTransversal.restartPhase_transversal
        r o₁ o₂ _ _ _ _ _ start hstart)
    rw [hzero]
    exact mul_nonneg (by positivity) (Arlib.Probability.FinDist.coe_nonneg _ _)
  · -- Concrete route: nontransversal endpoints are eliminated above by the
    -- actual restart invariant. On transversals, restriction alone is
    -- insufficient: one must realise the positive-time trace kernel, prove
    -- its mixing bound, iterate the stored levels, and transfer the
    -- uncapped endpoint law to this covered finite suffix. No such trace
    -- kernel/mixing-to-operational bridge exists in the current imports.
    -- BLOCKER: positive-time trace mixing and its capped finite-suffix bridge.
    sorry

end CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-08 · retained · live handoff recorded-path-domination-20261008-wave1 was mechanically rejected; the warm transversal comparison remains owned here. Restriction proves only zero off the transversal class, not its endpoint density bound.

* 2026-10-08 · decomposed · exact finite-suffix restart marginal; invalid endpoints have zero mass by restartPhase_transversal. The transversal warm endpoint comparison needs the trace mixing and finite-bit transfer.
-/
