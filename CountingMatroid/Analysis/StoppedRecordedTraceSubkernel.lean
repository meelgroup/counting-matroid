import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.ChainStepIntervalReplay
import CountingMatroid.Analysis.ChainStepNoninvalid
import CountingMatroid.Analysis.ObservePhaseIntervalReplay
import CountingMatroid.Analysis.FiniteTapePrefixBound
import CountingMatroid.Analysis.RecordedTraceContinuationBound

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Stopped-prefix composition for recorded observations. The initializer is an
arbitrary successful interval-local operation returning a transversal and an
adaptive cursor. Coverage is an explicit deterministic hypothesis; the
one-step subkernel bound is an explicit stochastic hypothesis. These separate
inputs keep the composition independent of the schedule's bit budget and of
warm restart estimates. Successful initializer fibers are disintegrated at
their ending cursor, covered transition continuations are bounded by their
ideal products, and the unused last ideal transition is summed out. Zero
observations and overrun initializers are handled separately.
-/
namespace CountingMatroid.Analysis.StoppedRecordedTraceSubkernel

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RecordedObservationTrajectory
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.RecordedTraceContinuationBound

/-- INTERNAL: Summing out the unused last vertex leaves the weight of the
specified observation prefix, with its arbitrary initial weight. -/
theorem path_prefix_mass {α : Type} [Fintype α] [DecidableEq α]
    (P : Arlib.MarkovChains.FinChain α) (states : List α) (w : α → ℝ) :
    (∑ path : Fin (states.length + 1) → α,
      if List.ofFn (fun i : Fin states.length => path i.castSucc) = states
      then w (path 0) * ∏ i : Fin states.length, P (path i.castSucc) (path i.succ)
      else 0) =
    match states with
    | [] => ∑ x, w x
    | a :: rest => w a * continuationWeight P a rest := by
  classical
  induction states generalizing w with
  | nil =>
    simp only [List.length_nil, List.ofFn_zero, ite_true, Fin.prod_univ_zero, mul_one]
    exact Equiv.sum_comp (Equiv.funUnique (Fin 1) α) w
  | cons a rest ih =>
    simp only [List.length_cons]
    rw [StationaryPathMoment.sum_paths_cons rest.length]
    simp only [List.ofFn_succ, Fin.castSucc_zero, Fin.cons_zero,
      ← Fin.succ_castSucc, Fin.cons_succ, List.cons.injEq]
    simp_rw [Fin.prod_univ_succ]
    simp only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, ← Fin.succ_castSucc]
    rw [Finset.sum_eq_single a]
    · have hfactor : (∑ path : Fin (rest.length + 1) → α,
          if a = a ∧ List.ofFn (fun i : Fin rest.length => path i.castSucc) = rest
          then w a * (P a (path 0) *
            ∏ i : Fin rest.length, P (path i.castSucc) (path i.succ)) else 0) =
          w a * (∑ path : Fin (rest.length + 1) → α,
            if List.ofFn (fun i : Fin rest.length => path i.castSucc) = rest
            then P a (path 0) *
              ∏ i : Fin rest.length, P (path i.castSucc) (path i.succ) else 0) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro path _
        split_ifs <;> simp_all
      rw [hfactor, ih]
      cases rest with
      | nil => simp only [P.sum_coe, continuationWeight, mul_one]
      | cons b tail => rfl
    · intro x _ hx
      simp only [hx, false_and, if_false, Finset.sum_const_zero]
    · simp

/-- INTERNAL: A fixed-start ideal path marginal is the product along the
recorded states, with the unused final transition summed out. -/
theorem ideal_prefix_mass {α : Type} [Fintype α] [DecidableEq α]
    (P : Arlib.MarkovChains.FinChain α) (N : ℕ) (states : List α)
    (hlen : states.length = N) (start : α) :
    (∑ path : Fin (N + 1) → α,
      if List.ofFn (fun i : Fin N => path i.castSucc) = states ∧ start = path 0
      then ∏ i : Fin N, P (path i.castSucc) (path i.succ) else 0) =
    match states with
    | [] => 1
    | a :: rest => if start = a then continuationWeight P a rest else 0 := by
  classical
  subst N
  calc
    _ = ∑ path : Fin (states.length + 1) → α,
        if List.ofFn (fun i : Fin states.length => path i.castSucc) = states
        then (if start = path 0 then 1 else 0) *
          ∏ i : Fin states.length, P (path i.castSucc) (path i.succ) else 0 := by
      apply Finset.sum_congr rfl
      intro path _
      split_ifs <;> simp_all
    _ = _ := by
      rw [path_prefix_mass P states (fun x => if start = x then 1 else 0)]
      cases states with
      | nil => simp
      | cons a rest => by_cases hs : start = a <;> simp [hs]

/-- INTERNAL: Remove the deterministic first record before applying the proved
covered transition-continuation bound. -/
theorem phase_trace_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (pref : List Bool) (u : ℕ) (state next : PairedSet n),
      state.card = n → (classifyState state).val ≠ .invalid →
      fairMass pref u (fun tape => ∃ stop, stop ≤ pref.length + u ∧
        (chainStep r o₁ o₂ tape s.drawTrials q weights state pref.length).val =
          some (next, stop)) ≤ P state next)
    (a : PairedSet n) (rest : List (PairedSet n))
    (hlen : s.observations = rest.length + 1)
    (head : List Bool) (t : ℕ) (start : PairedSet n × ℕ)
    (hcursor : start.2 = head.length)
    (hvalid : (classifyState start.1).val ≠ .invalid) :
    fairMass head t (fun tape => ∃ final : ObservationCursor n,
      final.bitCursor ≤ head.length + t ∧
      observePhaseTrace r o₁ o₂ tape s q weights start = some (final, a :: rest)) ≤
    (if start.1 = a then continuationWeight P a rest else 0) := by
  classical
  let current : ObservationCursor n :=
    ⟨start.1, start.2, (allocateCounts n).val, 0⟩
  let indices := (List.range rest.length).map Nat.succ
  have hfirst (tape : ℕ → Bool) :
      observePhaseTrace r o₁ o₂ tape s q weights start = (do
        let middle ← (recordObservation r o₁ o₂ s.ρ current).val
        let result ← recordedObservationTrace r o₁ o₂ tape s q weights indices (some middle)
        pure (result.1, middle.state :: result.2)) := by
    rw [observePhaseTrace, hlen, List.range_succ_eq_map]
    rfl
  cases hr : (recordObservation r o₁ o₂ s.ρ current).val with
  | none =>
    have hz : fairMass head t (fun tape => ∃ final : ObservationCursor n,
        final.bitCursor ≤ head.length + t ∧
        observePhaseTrace r o₁ o₂ tape s q weights start = some (final, a :: rest)) = 0 := by
      unfold fairMass
      simp only [hfirst, hr, Option.bind_eq_bind, Option.bind_none, reduceCtorEq, and_false,
        exists_false, if_false, Finset.sum_const_zero]
    rw [hz]
    split_ifs
    · exact continuationWeight_nonneg P a rest
    · exact le_rfl
  | some middle =>
    have hp := record_preserves r o₁ o₂ s.ρ current middle hr
    have hevent (tape : ℕ → Bool) :
        (∃ final : ObservationCursor n, final.bitCursor ≤ head.length + t ∧
          observePhaseTrace r o₁ o₂ tape s q weights start = some (final, a :: rest)) ↔
        (start.1 = a ∧ ∃ final : ObservationCursor n,
          final.bitCursor ≤ head.length + t ∧
          recordedObservationTrace r o₁ o₂ tape s q weights indices (some middle) =
            some (final, rest)) := by
      rw [hfirst, hr]
      simp only [Option.bind_eq_bind, Option.bind_some]
      cases ht : recordedObservationTrace r o₁ o₂ tape s q weights indices (some middle) with
      | none => simp
      | some result =>
        rcases result with ⟨finished, recorded⟩
        simp only [Option.bind_some, Option.pure_def, Option.some.injEq,
          Prod.mk.injEq, List.cons.injEq, hp.1]
        dsimp only [current]
        aesop
    by_cases ha : start.1 = a
    · rw [if_pos ha]
      have heq : fairMass head t (fun tape => ∃ final : ObservationCursor n,
          final.bitCursor ≤ head.length + t ∧
          observePhaseTrace r o₁ o₂ tape s q weights start = some (final, a :: rest)) =
          fairMass head t (fun tape => ∃ final : ObservationCursor n,
            final.bitCursor ≤ head.length + t ∧
            recordedObservationTrace r o₁ o₂ tape s q weights indices (some middle) =
              some (final, rest)) := by
        unfold fairMass
        simp only [hevent, ha, true_and]
      rw [heq]
      have hi := trace_continuation_bound r o₁ o₂ s q weights P hstep indices
        (by intro k hk; obtain ⟨j, _, rfl⟩ := List.mem_map.mp hk; omega)
        rest (by simp [indices]) head t middle
        (hp.2.trans hcursor) (by simpa only [hp.1] using hvalid)
      simpa only [hp.1, current, ha] using hi
    · rw [if_neg ha]
      unfold fairMass
      simp only [hevent, ha, false_and, if_false, Finset.sum_const_zero, le_refl]

/-- INTERNAL: Compose covered one-step subkernels after an interval-local
initializer without normalizing its successful endpoint fibers. All successful
completed traces fit in the given fair suffix, so no defaulted bits are counted
as fresh randomness. The last ideal transition is summed out.
TEXLINE: main.tex:1181-1187,1207-1212,1392-1421 -/
theorem stopped_recorded_trace_subkernel {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule)
    (q : ℚ) (weights : Multipliers n) (head : List Bool) (t : ℕ)
    (initialRun : (ℕ → Bool) → Option (PairedSet n × ℕ))
    (hreplay : ChainStepIntervalReplay.SuccessReplay initialRun Prod.snd head.length)
    (htrans : ∀ tape start, initialRun tape = some start →
      (classifyState start.1).val = .transversal)
    (hcovered : ∀ (suffix : List.Vector Bool t) start observed recorded,
      initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start →
      observePhaseTrace r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
        s q weights start = some (observed, recorded) →
      observed.bitCursor ≤ head.length + t)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : by
      classical
      exact ∀ (pref : List Bool) (u : ℕ) (state next : PairedSet n),
        state.card = n → (classifyState state).val ≠ .invalid →
        (∑ suffix : List.Vector Bool u,
          if ∃ stop : ℕ, stop ≤ pref.length + u ∧
            (chainStep r o₁ o₂ (fun i => ((pref ++ suffix.val)[i]?).getD false)
              s.drawTrials q weights state pref.length).val = some (next, stop)
          then 1 / (2 : ℝ) ^ u else 0) ≤ P state next)
    (start : PairedSet n × ℕ)
    (states : List.Vector (PairedSet n) s.observations) :
    by
    classical
    exact (∑ suffix : List.Vector Bool t,
      if initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start ∧
        ∃ observed : ObservationCursor n,
          observePhaseTrace r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
            s q weights start = some (observed, states.val)
      then 1 / (2 : ℝ) ^ t else 0) ≤
    (∑ suffix : List.Vector Bool t,
      if initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start
      then 1 / (2 : ℝ) ^ t else 0) *
    ∑ path : Fin (s.observations + 1) → PairedSet n,
      if List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val ∧
        start.1 = path 0
      then ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ) else 0 := by
  classical
  by_cases hzero : s.observations = 0
  · have hstates : states.val = [] :=
      List.length_eq_zero_iff.mp (states.2.trans hzero)
    have hpath : (∑ path : Fin (s.observations + 1) → PairedSet n,
        if List.ofFn (fun i : Fin s.observations => path i.castSucc) = states.val ∧
          start.1 = path 0
        then ∏ i : Fin s.observations, P (path i.castSucc) (path i.succ) else 0) = 1 := by
      simp only [hzero, hstates, List.ofFn_zero, true_and]
      rw [Finset.sum_eq_single (fun _ => start.1)]
      · simp [hzero]
      · intro path _ hne
        apply if_neg
        intro heq
        apply hne
        funext i
        have hi : i = 0 := Fin.ext (by
          have hi := i.isLt
          simp only [Fin.val_zero]
          omega)
        rw [hi, ← heq]
      · simp
    rw [hpath, mul_one]
    apply Finset.sum_le_sum
    intro suffix _
    simp [observePhaseTrace, hzero, recordedObservationTrace, hstates]
  · by_cases hcursor : start.2 ≤ head.length + t
    · cases hstates : states.val with
      | nil =>
        exact False.elim (hzero (by simpa only [hstates, List.length_nil] using states.2.symm))
      | cons a rest =>
        have hobs : s.observations = rest.length + 1 := by
          simpa only [hstates, List.length_cons] using states.2.symm
        rw [ideal_prefix_mass P s.observations (a :: rest)
          (by simpa only [List.length_cons] using hobs.symm) start.1]
        dsimp only
        suffices hmass : fairMass head t (fun tape => initialRun tape = some start ∧
          ∃ observed : ObservationCursor n,
            observePhaseTrace r o₁ o₂ tape s q weights start = some (observed, a :: rest)) ≤
          fairMass head t (fun tape => initialRun tape = some start) *
            (if start.1 = a then continuationWeight P a rest else 0) by
          delta fairMass finiteTape at hmass
          convert hmass using 1
          · apply Finset.sum_congr rfl
            intro bits _
            split_ifs <;> rfl
          · congr 1
            apply Finset.sum_congr rfl
            intro bits _
            split_ifs <;> rfl
        by_cases hstart : head.length ≤ start.2
        · apply stopped_fiber_bound head t initialRun Prod.snd hreplay start hstart hcursor
          · by_cases ha : start.1 = a
            · simpa only [if_pos ha] using continuationWeight_nonneg P a rest
            · simp only [if_neg ha, le_refl]
          · intro pref hinit
            have hpref : (head ++ pref.val).length = start.2 := by
              simp only [List.length_append, pref.2]
              omega
            have hbudget : (head ++ pref.val).length + (t - (start.2-head.length)) =
                head.length + t := by
              rw [hpref]
              omega
            have hvalid : (classifyState start.1).val ≠ .invalid := by
              rw [htrans (finiteTape (head ++ pref.val)) start hinit]
              intro heq
              cases heq
            have hcover : ∀ tail : List.Vector Bool (t - (start.2-head.length)),
                (∃ observed : ObservationCursor n,
                  observePhaseTrace r o₁ o₂ (finiteTape ((head ++ pref.val) ++ tail.val))
                    s q weights start = some (observed, a :: rest)) →
                ∃ observed : ObservationCursor n,
                  observed.bitCursor ≤ (head ++ pref.val).length +
                    (t - (start.2-head.length)) ∧
                  observePhaseTrace r o₁ o₂ (finiteTape ((head ++ pref.val) ++ tail.val))
                    s q weights start = some (observed, a :: rest) := by
              intro tail
              rintro ⟨observed, htrace⟩
              let suffix : List.Vector Bool t := ⟨pref.val ++ tail.val, by
                simp only [List.length_append, pref.2, tail.2]
                omega⟩
              have hinitFull : initialRun
                  (finiteTape ((head ++ pref.val) ++ tail.val)) = some start :=
                (hreplay (finiteTape (head ++ pref.val)) start hinit).2 _ (by
                  intro i _ hi
                  have hagree := finiteTape_append_agree (head ++ pref.val) [] tail.val i
                    (by rw [hpref]; exact hi)
                  simpa only [List.append_nil] using hagree)
              delta finiteTape at hinitFull htrace
              have hc := hcovered suffix start observed states.val
                (by simpa only [suffix, List.append_assoc] using hinitFull)
                (by simpa only [suffix, List.append_assoc, hstates] using htrace)
              exact ⟨observed, by rw [hbudget]; exact hc, htrace⟩
            exact (fairMass_mono _ _ _ _ hcover).trans
              (phase_trace_bound r o₁ o₂ s q weights P (by
                intro pref u state next hc hv
                delta fairMass finiteTape
                convert hstep pref u state next hc hv using 1
                apply Finset.sum_congr rfl
                intro bits _
                split_ifs <;> rfl) a rest hobs
                (head ++ pref.val) (t - (start.2-head.length)) start hpref.symm hvalid)
        · have hnone : ∀ tape, initialRun tape ≠ some start := by
            intro tape hinit
            exact hstart (hreplay tape start hinit).1
          unfold fairMass
          simp only [hnone, false_and, if_false, Finset.sum_const_zero, zero_mul, le_refl]
    · have hevent : ∀ suffix : List.Vector Bool t,
          ¬ (initialRun (fun i => ((head ++ suffix.val)[i]?).getD false) = some start ∧
            ∃ observed : ObservationCursor n,
              observePhaseTrace r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
                s q weights start = some (observed, states.val)) := by
        intro suffix
        rintro ⟨hinit, observed, htrace⟩
        have hproj := recorded_trace_observePhase r o₁ o₂
          (fun i => ((head ++ suffix.val)[i]?).getD false) s q weights start
        rw [htrace] at hproj
        have hmono := (ObservePhaseIntervalReplay.observePhase_success_interval
          r o₁ o₂ s q weights start
          (fun i => ((head ++ suffix.val)[i]?).getD false) observed hproj.symm).1
        exact hcursor (hmono.trans (hcovered suffix start observed states.val hinit htrace))
      simp only [hevent, if_false, Finset.sum_const_zero]
      apply mul_nonneg
      · apply Finset.sum_nonneg
        intro suffix _
        split_ifs <;> positivity
      · apply Finset.sum_nonneg
        intro path _
        split_ifs
        · exact Finset.prod_nonneg (fun i _ => P.coe_nonneg _ _)
        · exact le_rfl

end CountingMatroid.Analysis.StoppedRecordedTraceSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · closed stopped_recorded_trace_subkernel using the existing proved stopped-fiber and trace-continuation bounds; proved the ideal-prefix marginal and deterministic first-record reduction locally. The theorem statement and all original imports are preserved.

* 2026-10-09 · reduced · proved zero-observation and overrun-initializer cases. Atomwise sum comparison requires a false pointwise indicator bound; direct range-list induction retains the wrong initializer, counters, and state-vector length. Covered positive-length composition remains open and needs stopped-bind mass disintegration and a generalized continuation invariant.
-/
