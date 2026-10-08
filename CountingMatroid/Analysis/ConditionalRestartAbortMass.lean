import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.InitialRestartLaw
import CountingMatroid.Analysis.FiniteObservationMarkov
import CountingMatroid.Analysis.BoundedUniformAbortMass
import CountingMatroid.Analysis.RestartCostDrawCover

/-!
The phase-zero restart is proved abort-free. The positive-phase conclusion
uses the operational cost/draw-cover certificate in RestartCostDrawCover.
The finite Markov and union-bound reduction is proved, as are the covered
single-call and adaptive rejection-cap laws in BoundedUniformAbortMass.
The certificate's actual trace-excursion expectation and finite-block
reachability remain open; the theorem statement and tape are preserved.
-/

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

/-- INTERNAL: The finite counting part of the restart argument. An expected
cost certificate bounds cap overflow by Markov; K covered adaptive draw-site
families contribute K times their individual rejection-cap budget.
TEXLINE: main.tex:1230-1239,1415-1421 -/
theorem restart_abort_mass_of_cost_and_draw_cover
    (base : List Bool) (t K trials cap : ℕ) (hcap : 0 < cap)
    (M : ℚ) (hM : 0 ≤ M) (cost : List Bool → ℕ)
    (draws : Fin K → BoundedUniformAbortMass.DrawHistory base t trials)
    (bad : Set (List Bool))
    (hlen : bad ⊆ {bits : List Bool | bits.length = t})
    (hmoment : (∑ bits : List.Vector Bool t, (cost bits.val : ℚ)) / (2 : ℚ) ^ t ≤ M)
    (hcover : ∀ bits ∈ bad, cap ≤ cost bits ∨ ∃ k, (draws k).abortEvent bits) :
    (bad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
      ENNReal.ofReal ((M / (cap : ℚ) + (K : ℚ) * (1 / 2 : ℚ) ^ trials : ℚ) : ℝ) := by
  classical
  letI := Classical.propDecidable
  let tail := {bits : List Bool | bits.length = t ∧ cap ≤ cost bits}
  let drawBad := fun k : Fin K =>
    {bits : List Bool | bits.length = t ∧ (draws k).abortEvent bits}
  have htail : (tail.ncard : ℚ) / (2 : ℚ) ^ t ≤ M / (cap : ℚ) := by
    have hmarkov := FiniteObservationMarkov.finite_markov_card
      (fun bits : List.Vector Bool t => cap ≤ cost bits.val)
      (fun bits => (cost bits.val : ℚ)) (cap : ℚ)
      (fun _ => by positivity) (fun _ h => by exact_mod_cast h)
    have hcapq : (0 : ℚ) < cap := by exact_mod_cast hcap
    apply (le_div_iff₀ hcapq).mpr
    rw [show tail.ncard =
      (Finset.univ.filter (fun bits : List.Vector Bool t => cap ≤ cost bits.val)).card from
      (by simpa only [tail] using
        FiniteObservationMarkov.event_card_vectors t (fun bits => cap ≤ cost bits))]
    calc
      _ = (((Finset.univ.filter (fun bits : List.Vector Bool t =>
          cap ≤ cost bits.val)).card : ℚ) * cap) / (2 : ℚ) ^ t := by ring
      _ ≤ (∑ bits : List.Vector Bool t, (cost bits.val : ℚ)) / (2 : ℚ) ^ t :=
        div_le_div_of_nonneg_right hmarkov (by positivity)
      _ ≤ M := hmoment
  have htailMass := FiniteObservationMarkov.ennreal_mass_of_rat_bound t tail.ncard
    (M / (cap : ℚ)) htail
  have hsubset : bad ⊆ tail ∪ ⋃ k ∈ (Finset.univ : Finset (Fin K)), drawBad k := by
    intro bits hb
    rcases hcover bits hb with ht | ⟨k, hk⟩
    · exact Or.inl ⟨hlen hb, ht⟩
    · exact Or.inr (Set.mem_iUnion.mpr ⟨k,
        Set.mem_iUnion.mpr ⟨Finset.mem_univ k, ⟨hlen hb, hk⟩⟩⟩)
  have hfinite : (tail ∪ ⋃ k ∈ (Finset.univ : Finset (Fin K)), drawBad k).Finite :=
    (List.finite_length_eq Bool t).subset (by
      intro bits hb
      rcases hb with ht | hd
      · exact ht.1
      · obtain ⟨k, hd⟩ := Set.mem_iUnion.mp hd
        obtain ⟨_, hd⟩ := Set.mem_iUnion.mp hd
        exact hd.1)
  have hcard : bad.ncard ≤ tail.ncard + ∑ k, (drawBad k).ncard :=
    (Set.ncard_le_ncard hsubset hfinite).trans
      ((Set.ncard_union_le _ _).trans (Nat.add_le_add_left
        (Finset.univ.set_ncard_biUnion_le drawBad) _))
  have hdrawEq : ENNReal.ofReal (((K : ℚ) * (1 / 2 : ℚ) ^ trials : ℚ) : ℝ) =
      (K : ENNReal) * (1 / 2 : ENNReal) ^ trials := by
    push_cast
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast,
      ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
      ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
  calc
    _ ≤ ((tail.ncard + ∑ k, (drawBad k).ncard : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ t := mul_le_mul_left (Nat.cast_le.mpr hcard) _
    _ = (tail.ncard : ENNReal) * (1 / 2 : ENNReal) ^ t +
        ∑ k, ((drawBad k).ncard : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      rw [Nat.cast_add, Nat.cast_sum, add_mul, Finset.sum_mul]
    _ ≤ ENNReal.ofReal ((M / (cap : ℚ) : ℚ) : ℝ) +
        ∑ _k : Fin K, (1 / 2 : ENNReal) ^ trials :=
      add_le_add htailMass (Finset.sum_le_sum (fun k _ =>
        BoundedUniformAbortMass.adaptive_draw_abort_mass base t trials (draws k)))
    _ = ENNReal.ofReal ((M / (cap : ℚ) : ℚ) : ℝ) +
        ENNReal.ofReal (((K : ℚ) * (1 / 2 : ℚ) ^ trials : ℚ) : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdrawEq]
    _ = _ := by
      rw [Rat.cast_add, ENNReal.ofReal_add]
      · exact_mod_cast div_nonneg hM (by positivity : (0 : ℚ) ≤ cap)
      · positivity

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
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
      let M := 20 * (n : ℚ) ^ 2 * (s.L : ℚ) * (s.τ : ℚ)
      let bad := {suffix : List Bool | suffix.length = t ∧
        (∀ b < a + 1, FirstPhaseFailure.CertifiedPhase r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s b) ∧
        ∃ current : AnnealingCursor n,
          BoundedRunPhaseHistory.phaseHistory r o₁ o₂
            (fun i => ((pref ++ suffix)[i]?).getD false) s (a + 1) = some current ∧
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables (a + 1) current.bitCursor).val = none}
      have hτ : s.τ = 20 * n ^ 4 * (n * (s.L + 1) + 2) := by rfl
      have hτpos : 0 < s.τ := by rw [hτ]; positivity
      have hcapEq : s.restartCap = 2000 * (s.L + 1) ^ 2 * n ^ 2 * s.τ := by rfl
      have hcap : 0 < s.restartCap := by rw [hcapEq]; positivity
      have hconstruction : ∃ (cost : List Bool → ℕ)
          (draws : Fin (3 * s.restartCap) →
            BoundedUniformAbortMass.DrawHistory pref t s.drawTrials),
          (∑ bits : List.Vector Bool t, (cost bits.val : ℚ)) / (2 : ℚ) ^ t ≤ M ∧
          ∀ suffix ∈ bad, s.restartCap ≤ cost suffix ∨
            ∃ k, (draws k).abortEvent suffix := by
        exact RestartCostDrawCover.restart_cost_draw_cover n r M₁ M₂ o₁ o₂ p
          hn hfull hr h₁ h₂ hpositive (a + 1) (Nat.succ_pos a) hj pref hprefix
      obtain ⟨cost, draws, hmoment, hcover⟩ := hconstruction
      have hbound := restart_abort_mass_of_cost_and_draw_cover pref t
        (3 * s.restartCap) s.drawTrials s.restartCap hcap M (by positivity)
        cost draws bad (fun _ hb => hb.1) hmoment hcover
      dsimp only [M] at hbound
      rw [restart_markov_budget n p hn] at hbound
      simpa only [Nat.cast_mul, Nat.cast_ofNat] using hbound

end CountingMatroid.Analysis.ConditionalRestartAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · blocked · the parent elaborates through the open operational child. Live handoff `restart_cost_cover_r26_wave1` was mechanically rejected; both support files remain owned here, and this is not a completed restart-abort proof.

* r26 · handoff-ready · the parent uses `RestartCostDrawCover.restart_cost_draw_cover` for the operational moment and abort cover; all cardinality, Markov, adaptive rejection and schedule arithmetic steps are proved.

* r26 · reduced · proved the finite Markov-plus-adaptive-draw cover bound and used it in the parent; the sole remaining proof constructs the actual capped transition-cost moment and covered stopping-prefix families. The rejection-cap law is now proved separately.

* recovery · reduced · proved `restart_markov_budget` from the actual schedule and used the existing rational-to-ENNReal mass bridge; `exact?` found no proof of the residual positive-phase suffix estimate. No new open helper.

* r24 · attempted · phase zero is empty by the proved fresh restart law; exposing positive-phase folds leaves the uncapped return-time expectation and capped-draw finite-suffix coupling.
-/
