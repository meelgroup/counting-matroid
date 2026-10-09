import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.RestartPhaseTransversal

set_option autoImplicit false

namespace CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.StationaryMeanIdentities

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

/-- INTERNAL: The deterministic capped restart pushed forward from a finite
fair suffix is a subprobability law supported on transversals. Aborts retain
zero mass, and no independence or coverage assertion is needed here.
TEXLINE: main.tex:1163-1176,1207-1212 -/
theorem restart_suffix_mass_subprobability {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (j : ℕ)
    (current : AnnealingCursor n) (pref : List Bool) (t : ℕ) :
    (∀ state, 0 ≤ restartSuffixMass r o₁ o₂ s j current pref t state) ∧
    (∑ state, restartSuffixMass r o₁ o₂ s j current pref t state) ≤ 1 ∧
    (∀ state, (classifyState state).val ≠ .transversal →
      restartSuffixMass r o₁ o₂ s j current pref t state = 0) := by
  classical
  let R := fun suffix : List.Vector Bool t =>
    (restartPhase r o₁ o₂
      (fun i => ((pref ++ suffix.val)[i]?).getD false)
      s current.tables j current.bitCursor).val
  refine ⟨?_, ?_, ?_⟩
  · intro state
    unfold restartSuffixMass
    exact Finset.sum_nonneg fun _ _ => by split_ifs <;> positivity
  · unfold restartSuffixMass
    rw [Finset.sum_comm]
    calc
      (∑ suffix : List.Vector Bool t, ∑ state : PairedSet n,
        if (R suffix).map Prod.fst = some state then 1 / (2 : ℝ) ^ t else 0) ≤
          ∑ _suffix : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
        apply Finset.sum_le_sum
        intro suffix _
        cases hR : R suffix with
        | none => simp
        | some result => simp
      _ = 1 := by
        simp only [Finset.sum_const, Finset.card_univ, card_vector,
          Fintype.card_bool, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
        field_simp
  · intro state hinvalid
    unfold restartSuffixMass
    apply Finset.sum_eq_zero
    intro suffix _
    apply if_neg
    intro hstate
    obtain ⟨start, hstart, heq⟩ := Option.map_eq_some_iff.mp hstate
    change start.1 = state at heq
    exact hinvalid (heq ▸ RestartPhaseTransversal.restartPhase_transversal
      r o₁ o₂ _ _ _ _ _ start hstart)

end CountingMatroid.Analysis.SuccessfulPrefixRestartEndpointMass
