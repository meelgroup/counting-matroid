import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.ChainStepIntervalReplay
import CountingMatroid.Analysis.ChainStepNoninvalid
import CountingMatroid.Analysis.ObservePhaseIntervalReplay
import CountingMatroid.Analysis.FiniteTapePrefixBound

set_option autoImplicit false

/-!
Stopped-prefix composition for recorded observations. The initialRunr is an
arbitrary successful interval-local operation returning a transversal and an
adaptive cursor. Coverage is an explicit deterministic hypothesis; the
one-step subkernel bound is an explicit stochastic hypothesis. These separate
inputs keep the composition independent of the schedule's bit budget and of
warm restart estimates. The zero-observation and overrun-initializer cases
are proved; composition for covered nonempty observations remains open.
-/
namespace CountingMatroid.Analysis.StoppedRecordedTraceSubkernel

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RecordedObservationTrajectory

/-- INTERNAL: Compose covered one-step subkernels after an interval-local
initialRunr without normalizing its successful endpoint fibers. All successful
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
    · -- Route attempted: compare suffix atoms using sum_le_sum after distributing
      -- the endpoint mass. This leaves an indicator bounded by a path probability,
      -- which is false pointwise. The valid comparison must instead partition
      -- the initialRunr fiber by its consumed prefix, use interval replay to make
      -- each cell a full suffix cylinder, then induct on recordedObservationTrace.
      -- hcovered and successful interval replay ensure every induction step uses
      -- coveredChainStepMass rather than randomness from the defaulted tape tail.
      -- A second compiled route unfolded observePhaseTrace and inducted on
      -- its range list. The tail induction keeps the original initializer,
      -- zero counts, and full states vector, so it cannot apply to the returned
      -- ObservationCursor and shorter recorded list. It needs a generalized
      -- continuation invariant, together with stopped-cylinder disintegration.
      -- BLOCKER: a finite stopped-bind mass inequality, giving the first
      -- success submass times a uniform bound on each fresh continuation;
      -- then a list-indexed trace induction carrying cursor, counts, valid
      -- n-element states, remaining list length, and covered final cursor.
      sorry
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

* 2026-10-09 · reduced · proved zero-observation and overrun-initializer cases. Atomwise sum comparison requires a false pointwise indicator bound; direct range-list induction retains the wrong initializer, counters, and state-vector length. Covered positive-length composition remains open and needs stopped-bind mass disintegration and a generalized continuation invariant.
-/
