import CountingMatroid.Analysis.BoundedRunOtherSteps
import CountingMatroid.Analysis.ScheduleResourceEnvelope
import CountingMatroid.Analysis.ObservationRoundDrawSites
import CountingMatroid.Analysis.PhaseChainWork

set_option autoImplicit false

/-!
The quantitative finite-block obligation for the concrete observation draw
stopping maps. The bound must account for all earlier actual phase updates,
restart attempts, and k observations. The proof remains open; positivity is
already proved separately in ObservationRoundDrawSites.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSiteCovered

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Every stopped observation draw has its cursor after the
external consumed prefix and enough remaining block space for all trials.
TEXLINE: main.tex:1350-1390,1392-1421 -/
theorem observation_round_draw_site_covered (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref)
    (k : ℕ) (hk : k < (CountingMatroid.Interface.Pseudocode.setup n p).observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let t := m - pref.length
    ∀ site suffix, suffix.length = t → ∀ d,
      observationDrawSite n r o₁ o₂ p j pref k site suffix = some d →
      pref.length ≤ d.1 ∧ d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ m := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  dsimp only
  intro site suffix hlen d hsite
  unfold observationDrawSite at hsite
  simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at hsite
  obtain ⟨current, hhistory, start, hrestart, reached, hobserve, hsite⟩ := hsite
  let tape : ℕ → Bool := fun i => ((pref ++ suffix)[i]?).getD false
  let S := BoundedRunPhase.runSize n s
  have hS : 5 ≤ S := by
    dsimp [S, BoundedRunPhase.runSize, binaryRatLength, binaryNatLength]
    omega
  have h6 : 6 ≤ S ^ 10 := by
    have hp := Nat.pow_le_pow_left hS 10
    norm_num at hp
    omega
  let initial := BoundedRunPhaseHistory.initialCursor n s
  have hinit : BoundedRunPhase.PhaseSizeInvariant S 0 (some initial) := by
    intro cur hcur
    cases Option.some.inj hcur
    dsimp [initial, BoundedRunPhaseHistory.initialCursor,
      Model.Operations.initialWeights, Model.Operations.allocateLearnedWeights]
    simp only [Nat.one_mul]
    change (∀ _ : DefectIndex n, binaryRatLength (4 : ℚ) ≤ S ^ 10) ∧
      (∀ (_ : ℕ) (_ : DefectIndex n), binaryRatLength (4 : ℚ) ≤ S ^ 10) ∧
      binaryRatLength (1 : ℚ) ≤ S ^ 10
    have hfour : binaryRatLength (4 : ℚ) = 6 := by decide
    have hone : binaryRatLength (1 : ℚ) = 4 := by decide
    rw [hfour, hone]
    exact ⟨fun _ => h6, fun _ _ => h6, by omega⟩
  have hscan := BoundedRunOtherSteps.phaseFold_work_and_size r o₁ o₂ tape s
    (ScheduleResourceEnvelope.schedule_rho_nonneg n p) j 0 (by dsimp only [s]; omega)
    (some initial) hinit
  have hhistorySize : BoundedRunPhase.PhaseSizeInvariant S j
      (BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j) := by
    simpa only [Nat.zero_add, BoundedRunPhaseHistory.phaseHistory,
      Arlib.Computation.Charged.repeatFor, List.range_eq_range'] using hscan.2
  have hcoarse := hhistorySize current hhistory
  let K := binaryRatLength 1 + n * binaryRatLength (s.ρ ^ j) + (j + 1) * S ^ 10
  have hweightBudget (state : PairedSet n) (kind : StateKind n) :
      ∀ w, (weightOfKind r o₁ o₂ (s.ρ ^ j) current.currentWeights state kind).val = some w →
        binaryRatLength w ≤ 2 * K :=
    (PhaseChainWork.weightOfKind_work_size r o₁ o₂ (s.ρ ^ j)
      current.currentWeights state kind K (by dsimp [K]; omega)
      (fun index => (hcoarse.1 index).trans (by dsimp [K]; omega))).2
  -- The existing phase-size invariant supplies a real stored-table bound,
  -- but its (j+1)*runSize^10 budget does not fit blockLength's quartic width.
  -- This second route therefore cannot replace the tighter count-ratio
  -- update invariant needed by the paper's multiplier-bit calculation.
  -- FinishPhaseWeightsSize.finishPhase_weights_length_le supplies the
  -- per-phase increment n*n*(4*(observations+4)); it still needs to be
  -- iterated through this actual history and its stored-table writes.
  -- The direct drawCalls-based cursor route also needs the global restart-attempt invariant:
  -- multiplying restartCap separately by j*tau would exceed drawCalls.
  unfold CountingMatroid.Model.Run.blockLength
  sorry

end CountingMatroid.Analysis.ObservationRoundDrawSiteCovered

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r27 · refined blocker · applied the proved phase-fold size invariant and instantiated weightOfKind_work_size; the resulting (j+1)*runSize^10 bound is too coarse for the fixed quartic tape width, so a tighter multiplier-update bound remains necessary.

* r27 · attempted · unfolded the actual stopped-site history and coarse block budget; PhaseChainWork's per-weight bound requires a quantitative stored-table length invariant and a phase-global restart-attempt count, neither supplied by value-only good multipliers.
-/
