import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List
import CountingMatroid.Analysis.FirstPhaseFailure
import CountingMatroid.Analysis.InitialRestartLaw
import CountingMatroid.Analysis.BoundedRunResourceEnvelope
import CountingMatroid.Analysis.EmpiricalPhaseCertificate

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapePhaseControl

open CountingMatroid.Model

/-- INTERNAL: A completed run admits empirical phase ratios obeying the
paper's relative ratio bounds and multiplying to its actual output. A proof
from the program should take these ratios from the successive `finishPhase`
results, using the learned tables from the same execution.
TEXLINE: main.tex:1190-1205,1290-1304 -/
def AccurateRatioProduct (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (tape : ℕ → Bool) : Prop :=
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let C := fun j => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)
  ∃ R : ℕ → ℚ,
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
      (2 : ℚ) ^ n * (∏ j ∈ Finset.range s.L, R j) ∧
    ∀ j < s.L,
      (1 - s.η) / (1 + s.η) ≤ R j / (C (j + 1) / C j) ∧
      R j / (C (j + 1) / C j) ≤ (1 + s.η) / (1 - s.η)

/-- INTERNAL: A nonzero capped finite-tape run fails to admit accurate
empirical ratios with probability at most one eighth. The intended witness
is the sequence of `finishPhase` ratios in `Program.boundedRun`.
The deterministic certificate extraction and first-failure union bound are
proved here. `EmpiricalPhaseCertificate` separates the raw restart and
correlated-observation estimates from deterministic finishing and learned-table
preservation. Its scalar arithmetic and exact once-per-index finishing
are proved in `RelativeObservationBounds` and `FinishPhaseEmpiricalUpdate`.
The remaining local stochastic obligation bounds failure of raw estimates,
including capped draws and adaptive finite-tape coverage. `InitialRestartLaw`
retains the proved phase-zero fresh-prefix/suffix identity.
`FirstPhaseFailure` supplies the operational certificates and counting cover.
TEXLINE: main.tex:1207-1296,1392-1427 -/
theorem finite_tape_inaccurate_ratios (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    (Set.ncard {bits : List Bool | bits.length = m ∧
      CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s ≠ 0 ∧
      ¬ AccurateRatioProduct n r o₁ o₂ p
        (fun i => (bits[i]?).getD false)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let m := CountingMatroid.Model.Run.blockLength n r p
  have certified_product (tape : ℕ → Bool)
      (hc : ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂ tape s j) :
      AccurateRatioProduct n r o₁ o₂ p tape := by
    let weights := (CountingMatroid.Model.Operations.initialWeights n).val
    let initial : CountingMatroid.Program.AnnealingCursor n :=
      ⟨(CountingMatroid.Model.Operations.allocateLearnedWeights n s.L weights).val,
        weights, 1, 0⟩
    let phase := BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s
    let history := fun j => (Arlib.Computation.Charged.repeatFor phase j
      (some initial)).val
    have fold_value
        (f : Option (CountingMatroid.Program.AnnealingCursor n) → ℕ →
          Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
            CountingMatroid.Model.Operations.Cell
            (Option (CountingMatroid.Program.AnnealingCursor n)))
        (l : List ℕ) (b : Option (CountingMatroid.Program.AnnealingCursor n)) :
        (Arlib.Computation.Charged.foldl f l b).val =
          l.foldl (fun acc j => (f acc j).val) b := by
      induction l generalizing b with
      | nil => rfl
      | cons a l ih =>
          simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons]
            using ih (f b a).val
    have hsucc (j : ℕ) : history (j + 1) = (phase j (history j)).val := by
      simp only [history, Arlib.Computation.Charged.repeatFor, fold_value,
        List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
    let R := fun j => if hj : j < s.L then Classical.choose (hc j hj) else 1
    have hR (j : ℕ) (hj : j < s.L) :
        (1 - s.η) / (1 + s.η) ≤
          R j / (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
            TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ∧
        R j / (TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (j + 1)) /
            TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ j)) ≤
          (1 + s.η) / (1 - s.η) ∧
        ∃ current next : CountingMatroid.Program.AnnealingCursor n,
          history j = some current ∧
          (phase j (some current)).val = some next ∧
          next.product = current.product * R j ∧
          FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s j current ∧
          (j + 1 < s.L →
            FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s (j + 1) next) := by
      simpa only [R, dif_pos hj] using Classical.choose_spec (hc j hj)
    have hproduct : ∀ k ≤ s.L,
        ∃ result : CountingMatroid.Program.AnnealingCursor n,
          history k = some result ∧
            result.product = ∏ j ∈ Finset.range k, R j := by
      intro k
      induction k with
      | zero =>
          intro _
          exact ⟨initial, rfl, by simp [initial]⟩
      | succ k ih =>
          intro hk
          obtain ⟨previous, hprevious, hp⟩ := ih (by omega)
          obtain ⟨current, next, hcurrent, hnext, hmul, _⟩ :=
            (hR k (by omega)).2.2
          have heq : current = previous := Option.some.inj (hcurrent.symm.trans hprevious)
          subst current
          refine ⟨next, ?_, ?_⟩
          · rw [hsucc, hprevious]
            exact hnext
          · rw [hmul, hp, Finset.prod_range_succ]
    obtain ⟨result, hresult, hprod⟩ := hproduct s.L le_rfl
    have hout : CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s =
        (2 : ℚ) ^ n * result.product := by
      simp only [CountingMatroid.Interface.Pseudocode.singleRun,
        CountingMatroid.Program.boundedRun, Arlib.Computation.Charged.val_bind]
      change (match history s.L with
        | none => pure (0, 0)
        | some result =>
          (do
            let power ← CountingMatroid.Program.natPower 2 n
            let scale ← CountingMatroid.Model.Operations.ratOfNat power
            let estimate ← CountingMatroid.Model.Operations.ratMul scale result.product
            pure (estimate, result.bitCursor))).val.1 = _
      rw [hresult]
      simp only [Arlib.Computation.Charged.val_bind,
        BoundedRunResourceEnvelope.natPower_value,
        CountingMatroid.Model.Operations.ratOfNat,
        CountingMatroid.Model.Operations.ratMul,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      norm_cast
    refine ⟨R, ?_, ?_⟩
    · exact hout.trans (congrArg ((2 : ℚ) ^ n * ·) hprod)
    · intro j hj
      exact ⟨(hR j hj).1, (hR j hj).2.1⟩
  let bad := fun j => {bits : List Bool | bits.length = m ∧
    FirstPhaseFailure.FirstFailure r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  let inaccurate : Set (List Bool) := {bits | bits.length = m ∧
    CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
      (fun i => (bits[i]?).getD false) s ≠ 0 ∧
    ¬ AccurateRatioProduct n r o₁ o₂ p (fun i => (bits[i]?).getD false)}
  let uncertified : Set (List Bool) := {bits | bits.length = m ∧
    ¬ ∀ j < s.L, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have hsubset : inaccurate ⊆ uncertified := by
    intro bits hb
    refine ⟨hb.1, ?_⟩
    intro hall
    exact hb.2.2 (certified_product _ hall)
  have hfinite : uncertified.Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : inaccurate.ncard ≤ ∑ j ∈ Finset.range s.L, (bad j).ncard :=
    (Set.ncard_le_ncard hsubset hfinite).trans
      (FirstPhaseFailure.uncertified_card_le_sum n r o₁ o₂ s m)
  have hcast : (inaccurate.ncard : ENNReal) ≤
      ∑ j ∈ Finset.range s.L, ((bad j).ncard : ENNReal) := by
    exact_mod_cast hcard
  have hη : 0 ≤ s.η := by
    change 0 ≤ p.ε / ((32 * (s.L + 1) : ℕ) : ℚ)
    exact div_nonneg p.ε_pos.le (Nat.cast_nonneg _)
  have hηsmall : s.η ≤ (1 / 3 : ℚ) := by
    have hformula : s.η = p.ε / (32 * ((s.L : ℚ) + 1)) := by
      change p.ε / ((32 * (s.L + 1) : ℕ) : ℚ) = _
      push_cast
      rfl
    rw [hformula]
    apply (div_le_iff₀ (by positivity : (0 : ℚ) < 32 * ((s.L : ℚ) + 1))).mpr
    have hL : (0 : ℚ) ≤ s.L := Nat.cast_nonneg _
    linarith [p.ε_lt_one]
  let rawBad := fun j => {bits : List Bool | bits.length = m ∧
    (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
      (fun i => (bits[i]?).getD false) s a) ∧
    ¬ EmpiricalPhaseCertificate.RawPhaseEstimates r o₁ o₂
      (fun i => (bits[i]?).getD false) s j}
  have hrawlocal (j : ℕ) (hj : j ∈ Finset.range s.L) :
      ((rawBad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        1 / (8 * ((s.L : ENNReal) + 1)) := by
    -- RECOVERY BOUNDARY: the event now concerns the actual restart and
    -- observePhase outputs BEFORE finishPhase, with relative error bounds
    -- for pZero, u, and each pDefect. The deterministic implication to an
    -- accurate ratio and good next stored tables is proved separately in
    -- EmpiricalPhaseCertificate.raw_phase_certified; it no longer forms
    -- part of this stochastic obligation.
    -- NEXT STEP: construct the uncapped fixed-kernel trajectory law for a
    -- reached good prefix; establish the stationary type identities and
    -- ideal-multiplier drift appearing in ObservationEstimates; prove the
    -- restart mean and warm correlated-average MSE, then transfer their
    -- union bound through capped draws and the remaining finite block.
    -- For j=0, InitialRestartLaw.restartPhase_zero and its proved fresh-bit
    -- split supply the starting law; no trace-cost estimate is required.
    -- For j>0, also prove the conditional trace restart mean. These are
    -- same-paper obligations, main.tex:1207-1285,1392-1427, not IID bounds.
    sorry
  have hlocal (j : ℕ) (hj : j ∈ Finset.range s.L) :
      ((bad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        1 / (8 * ((s.L : ENNReal) + 1)) := by
    have hsubsetRaw : bad j ⊆ rawBad j := by
      intro bits hb
      refine ⟨hb.1, hb.2.1, ?_⟩
      intro hraw
      exact hb.2.2 (EmpiricalPhaseCertificate.raw_phase_certified
        r o₁ o₂ _ s j hη hηsmall hraw)
    have hfiniteRaw : (rawBad j).Finite :=
      (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
    have hc : ((bad j).ncard : ENNReal) ≤ ((rawBad j).ncard : ENNReal) := by
      exact_mod_cast Set.ncard_le_ncard hsubsetRaw hfiniteRaw
    exact (mul_le_mul_of_nonneg_right hc bot_le).trans (hrawlocal j hj)
  change (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤ _
  calc
    (inaccurate.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
        (∑ j ∈ Finset.range s.L, ((bad j).ncard : ENNReal)) *
          (1 / 2 : ENNReal) ^ m := mul_le_mul_of_nonneg_right hcast bot_le
    _ = ∑ j ∈ Finset.range s.L,
        ((bad j).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := Finset.sum_mul ..
    _ ≤ ∑ _j ∈ Finset.range s.L, 1 / (8 * ((s.L : ENNReal) + 1)) :=
      Finset.sum_le_sum hlocal
    _ = (s.L : ENNReal) * (1 / (8 * ((s.L : ENNReal) + 1))) := by simp
    _ = (1 / 8 : ENNReal) * ((s.L : ENNReal) / ((s.L : ENNReal) + 1)) := by
      simp only [div_eq_mul_inv, one_mul,
        ENNReal.mul_inv (Or.inl (by norm_num : (8 : ENNReal) ≠ 0))
          (Or.inl (by norm_num : (8 : ENNReal) ≠ ⊤))]
      ac_rfl
    _ ≤ (1 / 8 : ENNReal) * 1 :=
      mul_le_mul_of_nonneg_left (ENNReal.div_le_of_le_mul (by simp)) bot_le
    _ = (1 / 8 : ENNReal) := mul_one _

end CountingMatroid.Analysis.FiniteTapePhaseControl

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved support · closed the exact once-per-index finishing lemma after rejected handoff. The new raw-estimate-to-certified-phase implication has no unproved children; the stochastic raw-estimate bound is the only remaining local gap.

* recovery · decomposed · replaced final-output certificate failure by raw empirical mean/restart failure; proved scalar ratio and learned-weight bounds and deterministic table preservation. Exact once-per-index finishing is isolated in FinishPhaseEmpiricalUpdate; the stochastic raw-estimate bound remains local. The assigned theorem statement and all existing imports are preserved.

* r19 · partial · proved and used the exact fresh-prefix/observation-suffix law for phase zero; the base observation concentration and positive-phase conditional restart/MSE estimates remain local to this theorem. All new support declarations are proved.

* r18 · partial · handoff mechanically rejected; retained all checked deterministic progress, proved the first-failure counting cover upstream, and kept the missing per-phase conditional probability estimate inside the assigned theorem. No new exported unproved helper remains.

* r18 · decomposed · checked deterministic extraction from actual charged phase prefixes and the finite union bound; the remaining conditional first-phase failure estimate is isolated and semantically used from `FirstPhaseFailure.finite_tape_first_phase_failure`.

* 2026-10-08 · blocked · fresh stdin probes with `exact?` and unfolding plus `aesop` leave the phase-fold event bound. Verified the pretest-cost dependency is irrelevant, the warm-start MSE/trace estimates remain missing, and the proved fair-tape counting conversion is downstream. No new declarations or proof debt.
* r16 · blocked · live handoff admission was mechanically rejected with no further diagnostic; ownership remains here. Both unfolding with `aesop` and direct `exact?` failed on the missing phase probability bound.
* r16 · open · extracted the accurate-ratio witness probability bound; unfolding the actual bounded-run fold and `aesop` leave the conditional phase law and finite-tape coupling. The deterministic product implication is proved separately.
-/
