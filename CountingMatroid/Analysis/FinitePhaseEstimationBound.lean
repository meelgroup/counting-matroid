import CountingMatroid.Analysis.StationaryMeanLowerBound
import CountingMatroid.Analysis.FiniteObservationMarkov

set_option autoImplicit false

namespace CountingMatroid.Analysis.FinitePhaseEstimationBound

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.PhaseObservationExperiment
open CountingMatroid.Analysis.FiniteObservationMarkov
open CountingMatroid.Analysis.RelativeObservationBounds

/-- INTERNAL: The concrete observation ceiling makes the Markov union
bound at most the paper's per-phase estimation budget. Repeated diagonal
indicators enlarge the family to n²+2 ≤ 3n²; the numerical slack covers this.
TEXLINE: main.tex:1116-1126,1253-1266 -/
theorem schedule_estimation_budget (n : ℕ) (p : InputParams) (hn : 0 < n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    0 < s.η ∧ 0 < s.observations ∧
      (Fintype.card (Observable n) : ℚ) *
        (40000 * (n : ℚ) ^ 8 / s.observations) /
        (s.η * (1 / (20 * (n : ℚ) ^ 2))) ^ 2 ≤
          1 / (32 * ((s.L : ℚ) + 1)) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hη : 0 < s.η := by
    change 0 < p.ε / ((32 * (s.L + 1) : ℕ) : ℚ)
    exact div_pos p.ε_pos (by positivity)
  have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
  have hn2 : (1 : ℚ) ≤ (n : ℚ) ^ 2 := by nlinarith
  have hformula : s.observations =
      Int.toNat ((((10000000000 * (s.L + 1) *
        (natPower n 14).val : ℕ) : ℚ) / (s.η * s.η)).ceil) := by rfl
  rw [BoundedRunResourceEnvelope.natPower_value] at hformula
  let A : ℚ := 10000000000 * ((s.L : ℚ) + 1) * (n : ℚ) ^ 14
  have hceil : A / s.η ^ 2 ≤ (s.observations : ℚ) := by
    rw [hformula]
    have h : A / s.η ^ 2 ≤ ((A / s.η ^ 2).ceil.toNat : ℚ) :=
      Rat.le_ceil.trans (by
        have hcast := (Int.cast_le (R := ℚ)).mpr (Int.self_le_toNat (A / s.η ^ (2 : ℕ)).ceil)
        simpa only [Int.cast_natCast] using hcast)
    simpa only [A, pow_two, Nat.cast_mul, Nat.cast_add, Nat.cast_one,
      Nat.cast_pow, Nat.cast_ofNat] using h
  have hNq : (0 : ℚ) < s.observations :=
    (div_pos (by dsimp only [A]; positivity) (sq_pos_of_pos hη)).trans_le hceil
  have hN : 0 < s.observations := by exact_mod_cast hNq
  have hden : 0 < (s.η * (1 / (20 * (n : ℚ) ^ 2))) ^ 2 := by positivity
  have hcard : (Fintype.card (Observable n) : ℚ) ≤ 3 * (n : ℚ) ^ 2 := by
    simp only [Observable, Fintype.card_sum, Fintype.card_bool,
      Fintype.card_prod, Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    nlinarith
  refine ⟨hη, hN, ?_⟩
  apply (div_le_iff₀ hden).mpr
  rw [← mul_div_assoc]
  apply (div_le_iff₀ hNq).mpr
  have hsize : A ≤ (s.observations : ℚ) * s.η ^ 2 := (div_le_iff₀ (sq_pos_of_pos hη)).mp hceil
  have hL : (0 : ℚ) < (s.L : ℚ) + 1 := by positivity
  field_simp
  have hc : (Fintype.card (Observable n) : ℚ) * 40000 * (n : ℚ) ^ 12 *
      32 * ((s.L : ℚ) + 1) * 20 ^ 2 ≤ A := by
    calc
      _ ≤ (3 * (n : ℚ) ^ 2) * 40000 * (n : ℚ) ^ 12 *
          32 * ((s.L : ℚ) + 1) * 20 ^ 2 := by gcongr
      _ = 1536000000 * ((s.L : ℚ) + 1) * (n : ℚ) ^ 14 := by ring
      _ ≤ A := by dsimp only [A]; gcongr; norm_num
  exact hc.trans (by simpa only [mul_comm] using hsize)

/-- INTERNAL: A conditional second-moment bound for each concrete observable
implies the finite-tape relative-error budget, retaining all completed
operational outputs and bounding aborts elsewhere.
TEXLINE: main.tex:1253-1266 -/
theorem completed_failure_mass_le (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (pref : List Bool)
    (hmoment : ∀ index : Observable n,
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      (∑ suffix : List.Vector Bool t,
        observationSquaredError r o₁ o₂
          (fun i => ((pref ++ suffix.val)[i]?).getD false) s j index) /
          (2 : ℚ) ^ t ≤ 40000 * (n : ℚ) ^ 8 / s.observations) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      ObservationCompleted r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j ∧
      ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s j} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ 1 / (32 * ((s.L : ENNReal) + 1)) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let tape := fun suffix : List Bool => fun i : ℕ => ((pref ++ suffix)[i]?).getD false
  let bad := fun suffix : List Bool => ObservationCompleted r o₁ o₂ (tape suffix) s j ∧
    ¬ PhaseMeanCertificate.RawPhaseMeans r o₁ o₂ (tape suffix) s j
  let error := fun (suffix : List.Vector Bool t) (index : Observable n) =>
    observationSquaredError r o₁ o₂ (tape suffix.val) s j index
  let a : ℚ := 1 / (20 * (n : ℚ) ^ 2)
  obtain ⟨hη, hN, hbudget⟩ := schedule_estimation_budget n p hn
  have ha : 0 < a := by dsimp only [a]; positivity
  have hbad : ∀ suffix : List.Vector Bool t, bad suffix.val →
      ∃ index, (s.η * a) ^ 2 ≤ error suffix index := by
    intro suffix hb
    obtain ⟨current, observed, hdata, hg, hobs⟩ := hb.1
    have hfail : ¬ ∀ index : Observable n,
        RelativeEstimate s.η (observableMean r o₁ o₂ s j current index)
          (empiricalMean s observed index) := by
      intro hall
      exact hb.2 ((raw_means_iff_observation_data _ _ _ _ _ _).mpr
        ⟨current, observed, hdata, hg, hobs, hall⟩)
    obtain ⟨index, hi⟩ := not_forall.mp hfail
    refine ⟨index, ?_⟩
    dsimp only [error]
    simp only [observationSquaredError, hdata, if_pos (And.intro hg hobs)]
    exact relative_failure_square s.η a _ _ hη ha
      (StationaryMeanLowerBound.observable_mean_lower n r o₁ o₂ p hn j current hg index) hi
  have hcard := finite_family_markov (fun suffix : List.Vector Bool t => bad suffix.val)
    error (1 / (2 : ℚ) ^ t) ((s.η * a) ^ 2)
    (40000 * (n : ℚ) ^ 8 / s.observations) (by positivity) (by positivity)
    (fun suffix index => observation_squared_error_nonneg _ _ _ _ _ _ _)
    hbad (by intro index; simpa only [div_eq_mul_inv, one_mul] using hmoment index)
  rw [← event_card_vectors t bad] at hcard
  have hrat : (Set.ncard {suffix : List Bool | suffix.length = t ∧ bad suffix} : ℚ) /
      (2 : ℚ) ^ t ≤ 1 / (32 * ((s.L : ℚ) + 1)) := by
    have hcard' := hcard.trans hbudget
    simpa only [div_eq_mul_inv, one_mul] using hcard'
  have hmass := ennreal_mass_of_rat_bound t
    (Set.ncard {suffix : List Bool | suffix.length = t ∧ bad suffix}) _ hrat
  have hrhs : ENNReal.ofReal ((1 / (32 * ((s.L : ℚ) + 1)) : ℚ) : ℝ) =
      1 / (32 * ((s.L : ENNReal) + 1)) := by
    push_cast
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    simp [ENNReal.ofReal_mul, ENNReal.ofReal_add]
  rwa [hrhs] at hmass

end CountingMatroid.Analysis.FinitePhaseEstimationBound
