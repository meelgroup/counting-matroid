import CountingMatroid.Analysis.CappedRestartFinalTraceDomination
import CountingMatroid.Analysis.ScheduledTransversalTraceMixing
import CountingMatroid.Analysis.CappedReturnSubstationary
import CountingMatroid.Analysis.RestartAttemptBudget
import CountingMatroid.Analysis.ReturnAttemptTail

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Warm starts for every positive-time return of the restart that follows a
reached history with good stored multipliers. The cursor before return k of
stage i is the actual stopped restart cursor; its covered finite-suffix
state sublaw is at most four times the target-conditioned stationary law of
that stage's chain. The first stage starts from the fresh uniform transversal,
later stages from the scheduled factor-two mixing bound, and parameter drift
costs a further factor of two. Within a stage, capped returns are
sub-stationary. Aborted cursors carry no mass and are not renormalised.
-/
namespace CountingMatroid.Analysis.RestartStageWarmStart

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Analysis.CappedRestartFinalTraceDomination
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: The actual restart cursor before return k of stage i (stage i
runs at stored level i+1). Aborts are absorbing.
TEXLINE: main.tex:1163-1176 -/
noncomputable def stageCursor {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i k : ℕ) : Option (RestartCursor n) :=
  traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range k)
    (restart_phase_cursor r o₁ o₂ tape s tables i cursor)

/-- INTERNAL: A stage's cursors continue the earlier stopped restart. -/
theorem stage_cursor_bind {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i k : ℕ) :
    stageCursor r o₁ o₂ tape s tables cursor i k =
      (restart_phase_cursor r o₁ o₂ tape s tables i cursor).bind (fun c =>
        traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1)) (List.range k) (some c)) := by
  unfold stageCursor
  cases restart_phase_cursor r o₁ o₂ tape s tables i cursor with
  | none => exact trace_fold_none r o₁ o₂ tape s _ _ _
  | some c => rfl

/-- INTERNAL: The next stage starts where all τ returns of a stage end.
TEXLINE: main.tex:1163-1176 -/
theorem stage_cursor_next {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i : ℕ) :
    stageCursor r o₁ o₂ tape s tables cursor (i + 1) 0 =
      stageCursor r o₁ o₂ tape s tables cursor i s.τ := by
  change restart_phase_cursor r o₁ o₂ tape s tables (i + 1) cursor = _
  rw [restart_phase_cursor_succ, stage_cursor_bind]
  cases restart_phase_cursor r o₁ o₂ tape s tables i cursor with
  | none =>
      simp only [restart_stage, Arlib.Computation.Charged.val_pure, Option.bind_none]
  | some c =>
      rw [restart_stage_eq_trace_fold]
      rfl

/-- INTERNAL: Successful stage cursors replay their consumed interval. -/
theorem stage_cursor_success_interval {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor i k : ℕ) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => stageCursor r o₁ o₂ tape s tables cursor i k)
      RestartCursor.bitCursor cursor := by
  have h := ChainStepIntervalReplay.successReplay_bind
    (fun tape => restart_phase_cursor r o₁ o₂ tape s tables i cursor)
    (fun tape c => traceFold r o₁ o₂ tape s (s.ρ ^ (i + 1)) (tables (i + 1))
      (List.range k) (some c))
    RestartCursor.bitCursor RestartCursor.bitCursor cursor
    (restart_phase_cursor_success_interval r o₁ o₂ s tables i cursor)
    (fun c => trace_fold_success_interval r o₁ o₂ s _ _ (List.range k) c)
  intro tape out hout
  dsimp only at hout ⊢
  rw [stage_cursor_bind] at hout
  obtain ⟨h1, h2⟩ := h tape out hout
  exact ⟨h1, fun other hagree => by rw [stage_cursor_bind]; exact h2 other hagree⟩

/-- INTERNAL: Trace folds keep their cursors transversal. -/
theorem trace_fold_transversal {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs : List ℕ) (c out : RestartCursor n)
    (hc : (classifyState c.state).val = .transversal)
    (h : traceFold r o₁ o₂ tape s q w xs (some c) = some out) :
    (classifyState out.state).val = .transversal := by
  induction xs generalizing c with
  | nil => cases Option.some.inj h; exact hc
  | cons a xs ih =>
      rw [trace_fold_cons] at h
      obtain ⟨middle, hm, ht⟩ := Option.bind_eq_some_iff.mp h
      exact ih middle (RestartPhaseTransversal.traceReturn_transversal r o₁ o₂ tape s q w
        c middle hm) ht

/-- INTERNAL: Every stage cursor is a transversal.
TEXLINE: main.tex:1163-1176 -/
theorem stage_cursor_transversal {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor i k : ℕ) (c : RestartCursor n)
    (h : stageCursor r o₁ o₂ tape s tables cursor i k = some c) :
    (classifyState c.state).val = .transversal := by
  rw [stage_cursor_bind] at h
  obtain ⟨start, hs, ht⟩ := Option.bind_eq_some_iff.mp h
  apply trace_fold_transversal r o₁ o₂ tape s _ _ _ start c _ ht
  have hp := restart_phase_cursor_projection r o₁ o₂ tape s tables i cursor
  rw [hs] at hp
  exact RestartPhaseTransversal.restartPhase_transversal r o₁ o₂ tape s tables i cursor
    (start.state, start.bitCursor) hp

/-- INTERNAL: The shared-cap bit budget at a return boundary or between
attempts: every spent attempt paid for at most C fresh bits.
TEXLINE: main.tex:1392-1421 -/
def Budget {n : ℕ} (s : AnnealingSchedule) (base C : ℕ) (c : RestartCursor n) : Prop :=
  c.attempts ≤ s.restartCap ∧ c.bitCursor ≤ base + c.attempts * C

/-- INTERNAL: A permitted attempt keeps the budget. -/
theorem budget_step {n : ℕ} (s : AnnealingSchedule) (base C : ℕ) (c : RestartCursor n)
    (y : PairedSet n) (stop : ℕ) (hc : Budget s base C c)
    (ha : c.attempts < s.restartCap) (hstop : stop ≤ c.bitCursor + C) :
    Budget s base C ⟨y, stop, c.attempts + 1⟩ := by
  obtain ⟨_, hb⟩ := hc
  refine ⟨by dsimp only; omega, ?_⟩
  dsimp only
  rw [Nat.add_mul, Nat.one_mul]
  omega

/-- INTERNAL: A successful capped return scan keeps the budget. -/
theorem return_scan_budget {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base C : ℕ)
    (hC : ∀ (state : PairedSet n) (cursor : ℕ) (out : PairedSet n × ℕ),
      (chainStep r o₁ o₂ tape s.drawTrials q w state cursor).val = some out →
        out.2 ≤ cursor + C)
    (k : ℕ) (c out : RestartCursor n) (hc : Budget s base C c)
    (h : CappedTraceReturnSubkernel.returnScan r o₁ o₂ tape s q w k c = some out) :
    Budget s base C out := by
  induction k generalizing c with
  | zero => cases h
  | succ k ih =>
      simp only [CappedTraceReturnSubkernel.returnScan] at h
      split_ifs at h with ha
      obtain ⟨step, hs, ht⟩ := Option.bind_eq_some_iff.mp h
      have hb := budget_step s base C c step.1 step.2 hc ha (hC _ _ step hs)
      split_ifs at ht
      · cases Option.some.inj ht
        exact hb
      · exact ih _ hb ht

/-- INTERNAL: Successful trace folds keep the budget. -/
theorem trace_fold_budget {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base C : ℕ)
    (hC : ∀ (state : PairedSet n) (cursor : ℕ) (out : PairedSet n × ℕ),
      (chainStep r o₁ o₂ tape s.drawTrials q w state cursor).val = some out →
        out.2 ≤ cursor + C)
    (xs : List ℕ) (c out : RestartCursor n) (hc : Budget s base C c)
    (h : traceFold r o₁ o₂ tape s q w xs (some c) = some out) :
    Budget s base C out := by
  induction xs generalizing c with
  | nil => cases Option.some.inj h; exact hc
  | cons a xs ih =>
      rw [trace_fold_cons] at h
      obtain ⟨middle, hm, ht⟩ := Option.bind_eq_some_iff.mp h
      rw [CappedTraceReturnSubkernel.trace_return_scan_eq] at hm
      exact ih middle (return_scan_budget r o₁ o₂ tape s q w base C hC _ c middle hc hm) ht

/-- INTERNAL: Every stage cursor of a restart begun at `cursor` keeps the
budget measured from the end of its fresh scan.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem stage_cursor_budget {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor C i : ℕ)
    (hC : ∀ a ≤ i + 1, ∀ (state : PairedSet n) (start : ℕ) (out : PairedSet n × ℕ),
      (chainStep r o₁ o₂ tape s.drawTrials (s.ρ ^ a) (tables a) state start).val =
        some out → out.2 ≤ start + C)
    (k : ℕ) (c : RestartCursor n)
    (h : stageCursor r o₁ o₂ tape s tables cursor i k = some c) :
    Budget s (cursor + n) C c := by
  induction i generalizing k c with
  | zero =>
      rw [stage_cursor_bind] at h
      obtain ⟨start, hs, ht⟩ := Option.bind_eq_some_iff.mp h
      have hstart : Budget s (cursor + n) C start := by
        cases Option.some.inj hs
        simp only [Budget, InitialRestartLaw.freshTransversal_value, Nat.zero_mul,
          Nat.add_zero]
        exact ⟨Nat.zero_le _, le_rfl⟩
      exact trace_fold_budget r o₁ o₂ tape s _ _ (cursor + n) C (hC 1 le_rfl) _ start c
        hstart ht
  | succ i ih =>
      rw [stage_cursor_bind] at h
      obtain ⟨start, hs, ht⟩ := Option.bind_eq_some_iff.mp h
      have hprev : stageCursor r o₁ o₂ tape s tables cursor i s.τ = some start := by
        rw [← stage_cursor_next]
        exact hs
      have hstart := ih (fun a ha => hC a (by omega)) s.τ start hprev
      exact trace_fold_budget r o₁ o₂ tape s _ _ (cursor + n) C (hC (i + 2) le_rfl) _
        start c hstart ht

/-- INTERNAL: One covered operational chain step is dominated by the ideal
Metropolis kernel at the same level.
TEXLINE: main.tex:746-757,1392-1421 -/
theorem covered_step_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ a, 0 < w a) (head : List Bool) (u : ℕ) (x y : PairedSet n)
    (hv : (classifyState x).val ≠ .invalid) :
    fairMass head u (fun tape => ∃ stop, stop ≤ head.length + u ∧
      (chainStep r o₁ o₂ tape trials q w x head.length).val = some (y, stop)) ≤
      IdealExchangeChain.idealChain r o₁ o₂ q w hn hq hw x y := by
  have hb := CoveredChainStepSubkernel.covered_chain_step_subkernel r o₁ o₂ trials q
    w hn hq hw head u x y (RecordedTraceContinuationBound.classified_card x hv) hv
  convert hb using 1
  unfold FiniteStoppedFiberMass.fairMass CoveredChainStepSubkernel.coveredChainStepMass
  apply Finset.sum_congr rfl
  intro suffix _
  unfold FiniteStoppedFiberMass.finiteTape
  split_ifs <;> rfl

/-- INTERNAL: Covered finite-suffix state sublaw of the cursor before return k
of stage i. Aborted and uncovered cursors contribute nothing.
TEXLINE: main.tex:1207-1234,1392-1421 -/
noncomputable def stageMass {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) (x : PairedSet n) : ℝ :=
  fairMass pref t (fun tape => ∃ c, stageCursor r o₁ o₂ tape s tables cursor i k = some c ∧
    c.bitCursor ≤ pref.length + t ∧ c.state = x)

/-- INTERNAL: Stage masses are nonnegative. -/
theorem stage_mass_nonneg {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) (x : PairedSet n) :
    0 ≤ stageMass r o₁ o₂ s tables cursor pref t i k x :=
  fairMass_nonneg _ _ _

/-- INTERNAL: Stage masses vanish off the transversals. -/
theorem stage_mass_off {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) (x : PairedSet n)
    (hx : (classifyState x).val ≠ .transversal) :
    stageMass r o₁ o₂ s tables cursor pref t i k x = 0 := by
  classical
  unfold stageMass fairMass
  apply Finset.sum_eq_zero
  intro bits _
  apply if_neg
  rintro ⟨c, hc, _, hs⟩
  exact hx (hs ▸ stage_cursor_transversal r o₁ o₂ _ s tables cursor i k c hc)

/-- INTERNAL: At most one state carries a given outcome's indicator. -/
theorem option_state_sum_le {n : ℕ} (R : Option (RestartCursor n))
    (P : RestartCursor n → Prop)
    [hd : ∀ x : PairedSet n, Decidable (∃ c, R = some c ∧ P c ∧ c.state = x)]
    (a : ℝ) (ha : 0 ≤ a) :
    (∑ x : PairedSet n, if ∃ c, R = some c ∧ P c ∧ c.state = x then a else 0) ≤ a := by
  classical
  revert hd
  rcases R with _ | c <;> intro hd
  · simp [ha]
  · by_cases hP : P c
    · calc
        _ ≤ ∑ x : PairedSet n, if c.state = x then a else 0 := by
          apply Finset.sum_le_sum
          intro x _
          split_ifs with h1 h2
          · exact le_rfl
          · exfalso
            obtain ⟨c', hc', _, hs⟩ := h1
            cases Option.some.inj hc'
            exact h2 hs
          · exact ha
          · exact le_rfl
        _ = a := by rw [Finset.sum_ite_eq]; simp
    · have hz : ∀ x : PairedSet n, ¬ ∃ c', some c = some c' ∧ P c' ∧ c'.state = x := by
        rintro x ⟨c', hc', hp, _⟩
        cases Option.some.inj hc'
        exact hP hp
      simp only [hz, if_false, Finset.sum_const_zero]
      exact ha

/-- INTERNAL: A stage sublaw has total mass at most one. -/
theorem stage_mass_sum_le_one {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) :
    (∑ x, stageMass r o₁ o₂ s tables cursor pref t i k x) ≤ 1 := by
  classical
  unfold stageMass fairMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro bits _
      exact @option_state_sum_le n _ _ (fun _ => Classical.propDecidable _) (1 / (2 : ℝ) ^ t) (by positivity)
    _ = 1 := by simp [card_vector]

/-- INTERNAL: The cursors before return k of a stage are the stage's starting
sublaw pushed through k capped ideal returns, each granted the full cap.
TEXLINE: main.tex:1163-1176,1207-1212,1392-1421 -/
theorem stage_mass_fold {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t i k : ℕ) (hn : 0 < n) (hq : 0 < s.ρ ^ (i + 1))
    (hw : ∀ a, 0 < tables (i + 1) a) (hstart : pref.length ≤ cursor) (x : PairedSet n) :
    stageMass r o₁ o₂ s tables cursor pref t i k x ≤
      ∑ y, stageMass r o₁ o₂ s tables cursor pref t i 0 y *
        (iterate (returnWithin (IdealExchangeChain.idealChain r o₁ o₂ (s.ρ ^ (i + 1))
          (tables (i + 1)) hn hq hw)
          (Finset.univ.filter (fun z => (classifyState z).val = .transversal))
          s.restartCap) k).entry y x := by
  classical
  let q := s.ρ ^ (i + 1)
  let w := tables (i + 1)
  let P := IdealExchangeChain.idealChain r o₁ o₂ q w hn hq hw
  let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
  let K := iterate (returnWithin P A s.restartCap) k
  let f := fun tape : ℕ → Bool => restart_phase_cursor r o₁ o₂ tape s tables i cursor
  let E := fun tape (middle : RestartCursor n) => ∃ out : RestartCursor n,
    out.bitCursor ≤ pref.length + t ∧
    traceFold r o₁ o₂ tape s q w (List.range k) (some middle) = some out ∧ out.state = x
  have hf : ChainStepIntervalReplay.SuccessReplay f RestartCursor.bitCursor pref.length := by
    intro tape out hr
    have hi := restart_phase_cursor_success_interval r o₁ o₂ s tables i cursor tape out hr
    exact ⟨hstart.trans hi.1, fun other hagree =>
      hi.2 other (fun j hlo hhi => hagree j (hstart.trans hlo) hhi)⟩
  have hleft : stageMass r o₁ o₂ s tables cursor pref t i k x ≤
      fairMass pref t (fun tape => ∃ middle, f tape = some middle ∧ E tape middle) := by
    apply fairMass_mono
    intro bits h
    obtain ⟨c, hc, hcov, hs⟩ := h
    rw [stage_cursor_bind] at hc
    obtain ⟨middle, hm, ht⟩ := Option.bind_eq_some_iff.mp hc
    exact ⟨middle, hm, c, hcov, ht, hs⟩
  have hbound := FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound pref t f
    RestartCursor.bitCursor RestartCursor.state hf E
    (fun y => K.entry y x) (fun y => K.nonneg y x)
    (by
      intro bits middle _ hE
      obtain ⟨out, hc, hr, _⟩ := hE
      exact (trace_fold_success_interval r o₁ o₂ s q w (List.range k) middle _ out hr).1.trans hc)
    (by
      intro middle hlo hhi head hm
      have hhead : (pref ++ head.val).length = middle.bitCursor := by
        simp only [List.length_append, head.2]
        omega
      have hbudget : (pref ++ head.val).length + (t-(middle.bitCursor-pref.length)) =
          pref.length+t := by rw [hhead]; omega
      have hv : (classifyState middle.state).val ≠ .invalid := by
        have ht : (classifyState middle.state).val = .transversal := by
          have hs : stageCursor r o₁ o₂ (finiteTape (pref ++ head.val)) s tables cursor i 0 =
              some middle := hm
          exact stage_cursor_transversal r o₁ o₂ _ s tables cursor i 0 middle hs
        rw [ht]
        intro h
        cases h
      have hi := covered_trace_fold_bound r o₁ o₂ s q w P
        (fun head' u y z hy => covered_step_bound r o₁ o₂ s.drawTrials q w hn hq hw
          head' u y z hy)
        (List.range k) (pref ++ head.val)
        (t-(middle.bitCursor-pref.length)) middle hhead.symm hv x
      simp only [List.length_range, hbudget] at hi
      exact hi)
  refine hleft.trans (hbound.trans (le_of_eq ?_))
  apply Finset.sum_congr rfl
  intro y _
  rfl

/-- INTERNAL: Before any return, the first stage's covered sublaw is the fresh
uniform transversal on n new bits, so every state has mass at most 2^-n.
TEXLINE: main.tex:1163-1176,1242-1244 -/
theorem fresh_stage_mass_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (cursor : ℕ)
    (pref : List Bool) (t : ℕ) (hc : pref.length = cursor) (ht : n ≤ t)
    (x : PairedSet n) :
    stageMass r o₁ o₂ s tables cursor pref t 0 0 x ≤ 1 / (2 : ℝ) ^ n := by
  classical
  let F := fun pre : List.Vector Bool n =>
    (Finset.univ.image (fun i : Fin n => (i, pre.get i)) : PairedSet n)
  have hF : Function.Injective F := by
    intro a b heq
    apply List.Vector.ext
    intro i
    have hi : (i, a.get i) ∈ F b := by
      rw [← heq]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hi
    simp only [Prod.mk.injEq] at hj
    obtain ⟨rfl, h⟩ := hj
    exact h.symm
  have hmono : stageMass r o₁ o₂ s tables cursor pref t 0 0 x ≤
      fairMass pref t (fun tape => (freshTransversal n tape cursor).val.1 = x) := by
    apply fairMass_mono
    intro bits h
    obtain ⟨c, hcur, _, hs⟩ := h
    have hzero : stageCursor r o₁ o₂ (finiteTape (pref ++ bits.val)) s tables cursor 0 0 =
        some ⟨(freshTransversal n (finiteTape (pref ++ bits.val)) cursor).val.1,
          (freshTransversal n (finiteTape (pref ++ bits.val)) cursor).val.2, 0⟩ := rfl
    rw [hzero] at hcur
    cases Option.some.inj hcur
    exact hs
  rw [fairMass_split pref t n ht] at hmono
  refine hmono.trans ?_
  have hinner : ∀ pre : List.Vector Bool n,
      fairMass (pref ++ pre.val) (t - n)
        (fun tape => (freshTransversal n tape cursor).val.1 = x) ≤
        if F pre = x then 1 else 0 := by
    intro pre
    by_cases h : F pre = x
    · rw [if_pos h]
      exact ReturnAttemptTail.fairMass_le_one _ _ _
    · rw [if_neg h]
      unfold fairMass
      apply le_of_eq
      apply Finset.sum_eq_zero
      intro tail _
      apply if_neg
      intro hfx
      have hval := InitialRestartLaw.freshTransversal_after_prefix n pref pre tail.val
      rw [hc] at hval
      have heq : (freshTransversal n (finiteTape (pref ++ pre.val ++ tail.val)) cursor).val.1 =
          F pre := congrArg Prod.fst hval
      exact h (heq.symm.trans hfx)
  calc
    (∑ pre : List.Vector Bool n, 1 / (2 : ℝ) ^ n * fairMass (pref ++ pre.val) (t - n)
        (fun tape => (freshTransversal n tape cursor).val.1 = x)) ≤
        ∑ pre : List.Vector Bool n, 1 / (2 : ℝ) ^ n * (if F pre = x then 1 else 0) :=
      Finset.sum_le_sum fun pre _ =>
        mul_le_mul_of_nonneg_left (hinner pre) (by positivity)
    _ ≤ 1 / (2 : ℝ) ^ n := by
      by_cases hex : ∃ pre0, F pre0 = x
      · obtain ⟨pre0, h0⟩ := hex
        have hiff : ∀ pre, F pre = x ↔ pre = pre0 :=
          fun pre => ⟨fun h => hF (h.trans h0.symm), fun h => h ▸ h0⟩
        simp_rw [hiff]
        simp
      · push Not at hex
        simp only [hex, if_false, mul_zero, Finset.sum_const_zero]
        positivity

/-- INTERNAL: The target-conditioned stationary law of the transversal trace
at parameter q, extended by zero off the transversals.
TEXLINE: main.tex:1023-1037,1215-1218 -/
noncomputable def transversalLaw {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (x : PairedSet n) : ℝ :=
  if (classifyState x).val = .transversal then
    (((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ x).val) : ℚ) : ℝ) /
      (TransversalPartition.partitionSum r o₁ o₂ q : ℝ))
  else 0

/-- INTERNAL: At q = 1 every transversal has conditioned mass 2^-n.
TEXLINE: main.tex:1242-1244 -/
theorem transversal_law_one {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (x : PairedSet n) (hx : (classifyState x).val = .transversal) :
    transversalLaw r o₁ o₂ 1 x = 1 / (2 : ℝ) ^ n := by
  have hC : TransversalPartition.partitionSum r o₁ o₂ 1 = (2 : ℚ) ^ n := by
    simp [TransversalPartition.partitionSum]
  simp [transversalLaw, hx, hC]

/-- INTERNAL: One annealing step changes the conditioned transversal law by at
most a factor of two.
TEXLINE: main.tex:1219-1225 -/
theorem transversal_law_drift (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (i : ℕ) (x : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    transversalLaw r o₁ o₂ (s.ρ ^ i) x ≤ 2 * transversalLaw r o₁ o₂ (s.ρ ^ (i + 1)) x := by
  intro s
  by_cases hx : (classifyState x).val = .transversal
  · simp only [transversalLaw, hx, if_true]
    have hρ := AnnealingPartitionDrift.schedule_power_lower n p hn
    have hb := AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn i
    obtain ⟨hC, hhalf, hle, _⟩ := hb
    let d := n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ x).val
    have hd : d ≤ n := Nat.sub_le _ _
    have hρd : (1 / 2 : ℚ) ≤ s.ρ ^ d :=
      hρ.2.2.trans (pow_le_pow_of_le_one hρ.1.le hρ.2.1 hd)
    have hpow : (s.ρ ^ i) ^ d ≤ 2 * (s.ρ ^ (i + 1)) ^ d := by
      rw [pow_succ, mul_pow]
      have hnn : 0 ≤ (s.ρ ^ i) ^ d := pow_nonneg (pow_nonneg hρ.1.le _) _
      nlinarith
    have hC' : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (i + 1)) := by
      have : (0 : ℚ) < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ i) / 2 := by positivity
      exact this.trans_le hhalf
    have hq : ((s.ρ ^ i) ^ d : ℚ) / TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ i) ≤
        2 * ((s.ρ ^ (i + 1)) ^ d / TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (i + 1))) := by
      rw [← mul_div_assoc, div_le_div_iff₀ hC hC']
      have hnn : 0 ≤ (s.ρ ^ (i + 1)) ^ d := pow_nonneg (pow_nonneg hρ.1.le _) _
      have hnn' : 0 ≤ (s.ρ ^ i) ^ d := pow_nonneg (pow_nonneg hρ.1.le _) _
      calc
        (s.ρ ^ i) ^ d * TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (i + 1)) ≤
            (s.ρ ^ i) ^ d * TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ i) :=
          mul_le_mul_of_nonneg_left hle hnn'
        _ ≤ 2 * (s.ρ ^ (i + 1)) ^ d * TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ i) :=
          mul_le_mul_of_nonneg_right hpow hC.le
    exact_mod_cast hq
  · simp [transversalLaw, hx]

/-- INTERNAL: For the actual stationary law, the conditioned transversal law
is the target-restricted law divided by the target mass.
TEXLINE: main.tex:1023-1037,1215-1218 -/
theorem transversal_law_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ a, 0 < w a)
    (hC : 0 < TransversalPartition.partitionSum r o₁ o₂ q) (x : PairedSet n) :
    let π := IdealExchangeChain.operationalLaw r o₁ o₂ q w hq hw
    let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
    transversalLaw r o₁ o₂ q x = (1 / ∑ z ∈ A, π z) * (if x ∈ A then π x else 0) := by
  classical
  intro π A
  have hZ : (0 : ℝ) < (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) := by
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw).1
  have hmass : (∑ z ∈ A, π z) = (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) /
      (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) := by
    have hid := (StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw).2.1
    have hc := congrArg (fun a : ℚ => (a : ℝ)) hid
    simp only [StationaryMeanIdentities.typeMean, Rat.cast_div, Rat.cast_sum, apply_ite,
      Rat.cast_zero] at hc
    simpa only [A, Finset.sum_filter, π, IdealExchangeChain.operationalLaw, ite_div,
      zero_div, Finset.sum_div] using hc
  have hCr : (0 : ℝ) < (TransversalPartition.partitionSum r o₁ o₂ q : ℝ) := by
    exact_mod_cast hC
  by_cases hx : (classifyState x).val = .transversal
  · have hxA : x ∈ A := by simp [A, hx]
    have hW : StationaryMeanIdentities.stateWeight r o₁ o₂ q w x =
        q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ x).val) := by
      simp [StationaryMeanIdentities.stateWeight, hx, weightOfKind,
        CountingMatroid.Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value]
    simp only [transversalLaw, hx, if_true, hxA, hmass]
    change _ = _ * ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w x : ℝ) / _)
    rw [hW]
    field_simp
  · have hxA : x ∉ A := by simp [A, hx]
    simp [transversalLaw, hx, hxA]

/-- INTERNAL: The consumed prefix ends exactly at the restart cursor, and the
fresh suffix holds the fresh scan and the whole attempt allowance.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem history_prefix_facts (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    ∃ C : ℕ, pref.length = history.current.bitCursor ∧ n ≤ t ∧
      pref.length + t = CountingMatroid.Model.Run.blockLength n r p ∧
      history.current.bitCursor + n + s.restartCap * C ≤
        CountingMatroid.Model.Run.blockLength n r p ∧
      ∀ a ≤ s.L, ∀ (tape : ℕ → Bool) (state : PairedSet n) (cursor : ℕ)
        (out : PairedSet n × ℕ),
        (chainStep r o₁ o₂ tape s.drawTrials (s.ρ ^ a) (history.current.tables a)
          state cursor).val = some out → out.2 ≤ cursor + C := by
  intro s t
  obtain ⟨C, hCm, hCstep⟩ := RestartAttemptBudget.restart_attempt_budget n r o₁ o₂ p hn j hj
    pref history
  have hlen : pref.length = history.current.bitCursor := by
    have h := congrArg List.length history.consumed
    rw [List.length_take, history.length] at h
    omega
  refine ⟨C, hlen, ?_, ?_, hCm, hCstep⟩
  · dsimp only [t]
    omega
  · dsimp only [t]
    omega

/-- INTERNAL: Stored tables up to the current phase are positive.
TEXLINE: main.tex:1201-1205 -/
theorem history_table_pos (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (j : ℕ) (pref : List Bool)
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (a : ℕ) (ha : a ≤ j)
    (index : DefectIndex n) : 0 < history.current.tables a index := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  have hq : 0 < s.ρ ^ a := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 a
  have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a) :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn a).1
  exact (div_pos (div_pos hC
    (DefectPartitionPositive.defect_partition_pos r o₁ o₂ (s.ρ ^ a) hq index))
    (by norm_num : (0 : ℚ) < 4)).trans_le (history.good.1 a ha index).1

/-- INTERNAL: Before its first return, stage i has covered sublaw at most twice
the conditioned transversal law at level i: exactly the fresh law when i = 0,
and the scheduled mixing bound of the preceding stage otherwise.
TEXLINE: main.tex:1215-1225,1242-1244 -/
theorem stage_start_bound (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref)
    (i : ℕ) (hi : i < j) (x : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    stageMass r o₁ o₂ s history.current.tables history.current.bitCursor pref t i 0 x ≤
      2 * transversalLaw r o₁ o₂ (s.ρ ^ i) x := by
  classical
  intro s t
  obtain ⟨C, hlen, hnt, _, _, _⟩ := history_prefix_facts n r o₁ o₂ p hn j hj pref history
  by_cases hx : (classifyState x).val = .transversal
  case neg =>
    rw [stage_mass_off r o₁ o₂ s _ _ pref t i 0 x hx]
    simp [transversalLaw, hx]
  cases i with
  | zero =>
      have hf := fresh_stage_mass_le r o₁ o₂ s history.current.tables
        history.current.bitCursor pref t hlen hnt x
      rw [pow_zero, transversal_law_one r o₁ o₂ x hx]
      have hpos : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ n := by positivity
      linarith
  | succ i =>
      let tables := history.current.tables
      let q := s.ρ ^ (i + 1)
      have hq : 0 < q := pow_pos (AnnealingPartitionDrift.schedule_power_lower n p hn).1 _
      have hw : ∀ a, 0 < tables (i + 1) a :=
        history_table_pos n r o₁ o₂ p hn j pref history (i + 1) (by omega)
      let P := IdealExchangeChain.idealChain r o₁ o₂ q (tables (i + 1)) hn hq hw
      let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
      have hnext : stageMass r o₁ o₂ s tables history.current.bitCursor pref t (i + 1) 0 x =
          stageMass r o₁ o₂ s tables history.current.bitCursor pref t i s.τ x := by
        unfold stageMass
        simp only [stage_cursor_next]
      rw [hnext]
      have hfold := stage_mass_fold r o₁ o₂ s tables history.current.bitCursor pref t i s.τ
        hn hq hw hlen.le x
      have hxA : x ∈ TransversalTraceSpectralGap.transversalSet n := by
        simpa only [TransversalTraceSpectralGap.transversalSet, Finset.mem_filter,
          Finset.mem_univ, true_and] using hx
      apply PositiveTimeTraceKernel.endpoint_mass_le_of_capped_trace P A s.restartCap s.τ
        (fun y => stageMass r o₁ o₂ s tables history.current.bitCursor pref t i 0 y)
        (fun y => stage_mass_nonneg r o₁ o₂ s _ _ pref t i 0 y)
        (stage_mass_sum_le_one r o₁ o₂ s _ _ pref t i 0)
        (fun y hy => stage_mass_off r o₁ o₂ s _ _ pref t i 0 y (by
          simpa only [A, Finset.mem_filter, Finset.mem_univ, true_and] using hy))
        _ _ (by
          simp only [transversalLaw, hx, if_true]
          have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ q :=
            (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn (i + 1)).1
          apply mul_nonneg (by norm_num)
          apply div_nonneg
          · exact_mod_cast pow_nonneg hq.le _
          · exact_mod_cast hC.le) x hfold
      intro y hy
      have hyA : y ∈ TransversalTraceSpectralGap.transversalSet n := by
        simpa only [TransversalTraceSpectralGap.transversalSet] using hy
      have hmix := ScheduledTransversalTraceMixing.scheduled_transversal_trace_mixing
        n r M₁ M₂ o₁ o₂ p (i + 1) (tables (i + 1)) hn hfull hr h₁ h₂ (by omega) hw
        (history.good.1 (i + 1) (by omega)) y x hyA hxA
      simpa only [P, A, q, TransversalTraceSpectralGap.transversalSet, transversalLaw, hx,
        if_true] using hmix

/-- INTERNAL: Every return of every stage starts from a covered sublaw at most
four times the stage's target-conditioned stationary law.
TEXLINE: main.tex:1219-1234 -/
theorem stage_warm_start (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (history : RestartPrefixWitness n r o₁ o₂ p j pref)
    (i : ℕ) (hi : i < j) (k : ℕ)
    (hq : 0 < (CountingMatroid.Interface.Pseudocode.setup n p).ρ ^ (i + 1))
    (hw : ∀ a, 0 < history.current.tables (i + 1) a) (x : PairedSet n) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    let π := IdealExchangeChain.operationalLaw r o₁ o₂ (s.ρ ^ (i + 1))
      (history.current.tables (i + 1)) hq hw
    let A := Finset.univ.filter (fun z : PairedSet n => (classifyState z).val = .transversal)
    stageMass r o₁ o₂ s history.current.tables history.current.bitCursor pref t i k x ≤
      (4 / ∑ z ∈ A, π z) * (if x ∈ A then π x else 0) := by
  classical
  intro s t π A
  obtain ⟨C, hlen, hnt, _, _, _⟩ := history_prefix_facts n r o₁ o₂ p hn j hj pref history
  have hfold := stage_mass_fold r o₁ o₂ s history.current.tables history.current.bitCursor
    pref t i k hn hq hw hlen.le x
  apply hfold.trans
  have hmass : 0 ≤ ∑ z ∈ A, π z := Finset.sum_nonneg fun z _ => π.coe_nonneg z
  apply CappedReturnSubstationary.iterate_return_substationary _ A π
    (IdealExchangeChain.ideal_chain_stationary r o₁ o₂ _ _ hn hq hw) s.restartCap
    (4 / ∑ z ∈ A, π z) (div_nonneg (by norm_num) hmass)
    _ (fun y => stage_mass_nonneg r o₁ o₂ s _ _ pref t i 0 y)
  intro y
  have hC : 0 < TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ (i + 1)) :=
    (AnnealingPartitionDrift.partition_step_bounds n r o₁ o₂ p hn (i + 1)).1
  have hstart := stage_start_bound n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ j hj pref history
    i hi y
  have hdrift := transversal_law_drift n r o₁ o₂ p hn i y
  have heq := transversal_law_eq r o₁ o₂ (s.ρ ^ (i + 1)) (history.current.tables (i + 1))
    hq hw hC y
  change stageMass r o₁ o₂ s history.current.tables history.current.bitCursor pref t i 0 y ≤
    2 * transversalLaw r o₁ o₂ (s.ρ ^ i) y at hstart
  change transversalLaw r o₁ o₂ (s.ρ ^ i) y ≤
    2 * transversalLaw r o₁ o₂ (s.ρ ^ (i + 1)) y at hdrift
  change transversalLaw r o₁ o₂ (s.ρ ^ (i + 1)) y =
    (1 / ∑ z ∈ A, π z) * (if y ∈ A then π y else 0) at heq
  calc
    _ ≤ 2 * transversalLaw r o₁ o₂ (s.ρ ^ i) y := hstart
    _ ≤ 2 * (2 * transversalLaw r o₁ o₂ (s.ρ ^ (i + 1)) y) := by linarith
    _ = (4 / ∑ z ∈ A, π z) * (if y ∈ A then π y else 0) := by
      rw [heq]
      ring

end CountingMatroid.Analysis.RestartStageWarmStart

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · stage cursors with shared-cap budget and transversality, covered stage sublaws, composition through capped ideal returns, fresh-start and scheduled-mixing start bounds with parameter drift, and the factor-four warm start for every return.
-/
