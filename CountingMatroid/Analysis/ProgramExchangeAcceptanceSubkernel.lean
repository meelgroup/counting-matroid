import CountingMatroid.Analysis.RationalAcceptanceSubkernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Match the executable classifier, weight computation and rational
acceptance branch to a single ideal accept/reject outcome. -/
namespace CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.StationaryMeanIdentities

/-- INTERNAL: The deterministic weight/classifier part after the two index draws,
followed by the actual capped rational acceptance draw where required. -/
noncomputable def proposalAttempt {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state candidate : PairedSet n) (tape : ℕ → Bool) (start : ℕ) :
    Option (PairedSet n × ℕ) :=
  if (classifyState candidate).val = .invalid then some (state, start)
  else
    match (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val,
        (weightOfKind r o₁ o₂ q weights candidate (classifyState candidate).val).val with
    | some old, some new => rationalAccept tape trials (new / old) state candidate start
    | _, _ => none

/-- INTERNAL: Positive parameters give a positive actual weight value on every
classifier-valid state, with no matroid-oracle promise needed. -/
theorem classified_weight_positive {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state : PairedSet n) (hvalid : (classifyState state).val ≠ .invalid) :
    ∃ value, (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val =
      some value ∧ 0 < value := by
  cases hk : (classifyState state).val with
  | invalid => exact False.elim (hvalid hk)
  | transversal =>
      simp only [weightOfKind, Arlib.Computation.Charged.val_bind,
        Model.Operations.natSub, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_pure, BoundedRunResourceEnvelope.ratPower_value]
      exact ⟨_, rfl, pow_pos hq _⟩
  | defect i j =>
      have hij := ObservationRoundDrawSites.classified_defect_distinct state i j hk
      simp only [weightOfKind, dif_pos hij, Arlib.Computation.Charged.val_bind,
        Model.Operations.natSub, Model.Operations.multiplierRead,
        Model.Operations.ratMul, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure,
        BoundedRunResourceEnvelope.ratPower_value]
      exact ⟨_, rfl, mul_pos (hw ⟨i, j, hij⟩) (pow_pos hq _)⟩

/-- INTERNAL: Every successful rational branch retains a monotone cursor. -/
theorem rational_accept_monotone {α : Type} (tape : ℕ → Bool) (trials : ℕ)
    (ratio : ℚ) (state candidate next : α) (start stop : ℕ)
    (h : rationalAccept tape trials ratio state candidate start = some (next, stop)) :
    start ≤ stop := by
  unfold rationalAccept at h
  split at h
  · cases hd : (boundedUniform tape trials ratio.den start).val with
    | mk choice cursor =>
      cases choice with
      | none => simp [hd] at h
      | some value =>
        simp only [hd, Option.map_some, Option.some.injEq, Prod.mk.injEq] at h
        have hm := (BoundedUniformReplay.boundedUniform_interval_replay
          trials ratio.den start tape).1
        simpa only [hd, h.2] using hm
  · exact (Prod.mk.inj (Option.some.inj h)).2 ▸ Nat.le_refl start

/-- INTERNAL: Every successful proposal branch ends after its start cursor. -/
theorem proposal_attempt_monotone {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n) (state candidate next : PairedSet n)
    (tape : ℕ → Bool) (start stop : ℕ)
    (h : proposalAttempt r o₁ o₂ trials q weights state candidate tape start =
      some (next, stop)) : start ≤ stop := by
  unfold proposalAttempt at h
  split at h
  · exact (Prod.mk.inj (Option.some.inj h)).2 ▸ Nat.le_refl start
  · split at h
    · exact rational_accept_monotone tape trials _ state candidate next start stop h
    · cases h

/-- INTERNAL: The final executable proposal continuation is dominated by
one ideal Metropolis accept/reject outcome, including classifier rejection.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem proposal_attempt_covered_mass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state candidate next : PairedSet n) (hvalid : (classifyState state).val ≠ .invalid)
    (head : List Bool) (t : ℕ) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      proposalAttempt r o₁ o₂ trials q weights state candidate tape head.length =
        some (next, stop)) ≤
    exchangeOutcome state candidate next (min 1
      ((operationalLaw r o₁ o₂ q weights hq hw) candidate /
        (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  classical
  by_cases hc : (classifyState candidate).val = .invalid
  · have hz : (operationalLaw r o₁ o₂ q weights hq hw) candidate = 0 := by
      simp [operationalLaw, stateWeight, hc, weightOfKind]
    simp only [hz, zero_div, min_eq_right (by norm_num : (0 : ℝ) ≤ 1),
      exchangeOutcome, zero_mul, sub_zero, one_mul, zero_add]
    by_cases heq : state = next
    · rw [if_pos heq]
      exact fair_mass_le_one _ _ _
    · simp [fairMass, proposalAttempt, hc, heq, Option.some.injEq, Prod.mk.injEq]
  · obtain ⟨old, hold, hpos⟩ := classified_weight_positive r o₁ o₂ q weights hq hw state hvalid
    obtain ⟨new, hnew, hnewpos⟩ := classified_weight_positive r o₁ o₂ q weights hq hw candidate hc
    have hs : stateWeight r o₁ o₂ q weights state = old := by
      simp only [stateWeight, hold, Option.getD_some]
    have ht : stateWeight r o₁ o₂ q weights candidate = new := by
      simp only [stateWeight, hnew, Option.getD_some]
    have hnormal : (normalizer r o₁ o₂ q weights : ℝ) ≠ 0 := by
      exact_mod_cast (stationary_mean_identities r o₁ o₂ q 1 weights hq hw).1.ne'
    have hratio : (operationalLaw r o₁ o₂ q weights hq hw) candidate /
        (operationalLaw r o₁ o₂ q weights hq hw) state = (new / old : ℚ) := by
      change (stateWeight r o₁ o₂ q weights candidate : ℝ) / _ /
        ((stateWeight r o₁ o₂ q weights state : ℝ) / _) = _
      rw [hs, ht, div_div_div_cancel_right₀ hnormal, Rat.cast_div]
    have hevent (tape : ℕ → Bool) :
        proposalAttempt r o₁ o₂ trials q weights state candidate tape head.length =
          rationalAccept tape trials (new / old) state candidate head.length := by
      simp only [proposalAttempt, hc, if_false, hold, hnew]
    simp only [hevent, hratio]
    exact rational_accept_covered_mass head trials t (new / old)
      (div_pos hnewpos hpos).le state candidate next

end CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
