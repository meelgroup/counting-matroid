import CountingMatroid.Analysis.SuccessfulPrefixAbortBound
import CountingMatroid.Analysis.SuccessfulPrefixObservationMSE
import CountingMatroid.Analysis.SuccessfulPhasePrefixBound

set_option autoImplicit false

/-!
Finite-tape assembly of the conditional phase estimates. Successful histories
are disintegrated by their actual consumed prefixes; replay proves those
prefixes are prefix-free. The abort and completed-estimation budgets are
combined without assuming independence between phases or observations.
The quantitative input lemmas are owned by the successful-prefix modules.
-/

namespace CountingMatroid.Analysis.RawPhaseFailureMass

open CountingMatroid.Model

/-- INTERNAL: The conditional abort and observation-MSE estimates give the
unconditional raw phase-failure budget on actual finite tapes, restricted to
histories whose earlier phase certificates all hold.
TEXLINE: main.tex:1207-1285,1392-1427 -/
theorem raw_phase_failure_mass (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => (bits[i]?).getD false) s a) ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => (bits[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ 1 / (8 * ((s.L : ENNReal) + 1)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  let E := fun bits : List Bool =>
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
      (fun i => (bits[i]?).getD false) s j
  apply SuccessfulPhasePrefixBound.successful_phase_prefix_bound n r o₁ o₂ p j
    E (1 / (8 * ((s.L : ENNReal) + 1))) (fun _ h => h.1)
  intro pref hprefix
  let rawBad : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
    E (pref ++ suffix)}
  let aborted : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
    ¬ PhaseObservationExperiment.ObservationCompleted r o₁ o₂
      (fun i => ((pref ++ suffix)[i]?).getD false) s j}
  let inaccurate : Set (List Bool) := {suffix | suffix.length = m - pref.length ∧
    PhaseObservationExperiment.ObservationCompleted r o₁ o₂
      (fun i => ((pref ++ suffix)[i]?).getD false) s j ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
      (fun i => ((pref ++ suffix)[i]?).getD false) s j}
  have hcoverRaw : rawBad ⊆ aborted ∪ inaccurate := by
    intro suffix hs
    by_cases hdone : PhaseObservationExperiment.ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j
    · exact Or.inr ⟨hs.1, hdone, hs.2.2⟩
    · exact Or.inl ⟨hs.1, hs.2.1, hdone⟩
  have hfiniteUnion : (aborted ∪ inaccurate).Finite :=
    (List.finite_length_eq Bool (m - pref.length)).subset (by
      intro suffix hs
      exact hs.elim (fun h => h.1) (fun h => h.1))
  have hrawCard : rawBad.ncard ≤ aborted.ncard + inaccurate.ncard :=
    (Set.ncard_le_ncard hcoverRaw hfiniteUnion).trans
      (Set.ncard_union_le aborted inaccurate)
  have habort : (aborted.ncard : ENNReal) *
      (1 / 2 : ENNReal) ^ (m - pref.length) ≤
        3 / (32 * ((s.L : ENNReal) + 1)) := by
    exact SuccessfulPrefixAbortBound.conditional_successful_prefix_abort_mass
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
      j hj pref hprefix
  have hmoment : ∀ index : PhaseObservationExperiment.Observable n,
      (∑ suffix : List.Vector Bool (m - pref.length),
        PhaseObservationExperiment.observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
        (2 : ℚ) ^ (m - pref.length) ≤
          40000 * (n : ℚ) ^ 8 / s.observations := by
    intro index
    exact SuccessfulPrefixObservationMSE.conditional_successful_prefix_observation_mse
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive
      j hj pref hprefix index
  have hestimate := FinitePhaseEstimationBound.completed_failure_mass_le
    n r o₁ o₂ p hn j pref hmoment
  calc
    (rawBad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) ≤
        (aborted.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) +
        (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ (m - pref.length) := by
      rw [← add_mul, ← Nat.cast_add]
      gcongr
    _ ≤ 3 / (32 * ((s.L : ENNReal) + 1)) +
        1 / (32 * ((s.L : ENNReal) + 1)) := add_le_add habort hestimate
    _ = 1 / (8 * ((s.L : ENNReal) + 1)) := by
      rw [← ENNReal.add_div]
      norm_num only
      rw [show (32 : ENNReal) * ((s.L : ENNReal) + 1) =
        4 * (8 * ((s.L : ENNReal) + 1)) by ring]
      simp only [div_eq_mul_inv, ENNReal.mul_inv
        (Or.inl (by norm_num : (4 : ENNReal) ≠ 0))
        (Or.inl (by norm_num : (4 : ENNReal) ≠ ⊤))]
      rw [← mul_assoc, ENNReal.mul_inv_cancel (by norm_num) (by norm_num), one_mul]

end CountingMatroid.Analysis.RawPhaseFailureMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r25 · assembled · reused successful-prefix abort/MSE and deterministic replay to lift the raw conditional failure budget to the full finite tape.
-/
