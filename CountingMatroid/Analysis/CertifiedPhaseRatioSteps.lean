import CountingMatroid.Analysis.BoundedRunPhaseHistory
import CountingMatroid.Analysis.FirstPhaseFailure

set_option autoImplicit false

namespace CountingMatroid.Analysis.CertifiedPhaseRatioSteps

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Analysis.BoundedRunPhaseHistory

/-- INTERNAL: The stronger phase certificates used by conditional probability
analysis imply the local ratio steps of the actual operational history.
Positivity of every reached product is proved from initialization and the
certified ratio bounds; it is not an extra hypothesis on completed runs.
TEXLINE: main.tex:1273-1304 -/
theorem certified_phases_ratio_steps {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (hn : 0 < n)
    (tape : ℕ → Bool)
    (hcert : ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape
        (CountingMatroid.Interface.Pseudocode.setup n p) j) :
    ∀ j < (CountingMatroid.Interface.Pseudocode.setup n p).L,
      PhaseRatioStep r o₁ o₂ p tape j := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
  change ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j at hcert
  have hρ : 0 < s.ρ := by
    change 0 < 1 - 1 / ((2 * n : ℕ) : ℚ)
    push_cast
    have hnq : (1 : ℚ) ≤ n := by exact_mod_cast hn
    apply sub_pos.mpr
    apply (div_lt_one (by positivity : (0 : ℚ) < 2 * n)).mpr
    linarith
  have hη : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
    change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
    push_cast
    rfl
  have hηpos : 0 < s.η := by
    rw [hη]
    exact div_pos p.ε_pos (by positivity)
  have hηsmall : s.η < 1 := by
    rw [hη]
    apply (div_lt_one (by positivity : (0 : ℚ) < 32 * ((s.L : ℚ) + 1))).mpr
    have hL : (0 : ℚ) ≤ s.L := Nat.cast_nonneg _
    linarith [p.ε_lt_one]
  have hC : ∀ j, 0 < C j := by
    intro j
    apply Finset.sum_pos
    · intro A _
      exact pow_pos (pow_pos hρ j) _
    · exact Finset.univ_nonempty
  have hratioPos (j : ℕ) (ratio : ℚ)
      (hl : (1 - s.η) / (1 + s.η) ≤ ratio / (C (j + 1) / C j)) :
      0 < ratio := by
    have hden : 0 < C (j + 1) / C j := div_pos (hC _) (hC _)
    have hlo : 0 < (1 - s.η) / (1 + s.η) :=
      div_pos (sub_pos.mpr hηsmall) (by linarith)
    exact (mul_pos hlo hden).trans_le ((le_div_iff₀ hden).mp hl)
  have hstates (k : ℕ) (hk : k ≤ s.L) :
      ∃ current : AnnealingCursor n,
        phaseHistory r o₁ o₂ tape s k = some current ∧ 0 < current.product := by
    induction k with
    | zero => exact ⟨initialCursor n s, rfl, by norm_num [initialCursor]⟩
    | succ k ih =>
        obtain ⟨previous, hprevious, hpositive⟩ := ih (by omega)
        obtain ⟨ratio, hl, _, current, next, hcurrent, hnext, hmul, _⟩ :=
          hcert k (by omega)
        change phaseHistory r o₁ o₂ tape s k = some current at hcurrent
        have heq : current = previous :=
          Option.some.inj (hcurrent.symm.trans hprevious)
        subst current
        refine ⟨next, ?_, ?_⟩
        · rw [phaseHistory_succ, hprevious]
          exact hnext
        · rw [hmul]
          exact mul_pos hpositive (hratioPos k ratio hl)
  change ∀ j < s.L, PhaseRatioStep r o₁ o₂ p tape j
  intro j hj
  obtain ⟨previous, hprevious, hpositive⟩ := hstates j (by omega)
  obtain ⟨ratio, hl, hu, current, next, hcurrent, hnext, hmul, _⟩ := hcert j hj
  change phaseHistory r o₁ o₂ tape s j = some current at hcurrent
  have heq : current = previous := Option.some.inj (hcurrent.symm.trans hprevious)
  subst current
  have hnpos : 0 < next.product := by
    rw [hmul]
    exact mul_pos hpositive (hratioPos j ratio hl)
  have hquot : next.product / previous.product = ratio := by
    rw [hmul, mul_div_cancel_left₀ _ hpositive.ne']
  refine ⟨previous, next, hprevious, hnext, hpositive, hnpos, ?_⟩
  simpa only [hquot] using And.intro hl hu

end CountingMatroid.Analysis.CertifiedPhaseRatioSteps

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · proved · the good-multiplier phase certificates imply actual successful ratio steps; positivity of reached products follows inductively from their certified ratios. No probability bound or unproved declaration introduced.
-/
