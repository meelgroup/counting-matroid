import CountingMatroid.Analysis.CappedTraceReturnSubkernel
import CountingMatroid.Analysis.FiniteStoppedKernelBind
import CountingMatroid.Analysis.RestartPhaseTransversal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose covered operational positive-time returns while retaining their
shared attempt counter and the actual cursor between returns. -/
namespace CountingMatroid.Analysis.CappedTraceIterationSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel

/-- INTERNAL: The value of the absorbing-option fold of actual trace returns.
TEXLINE: main.tex:1163-1176 -/
noncomputable def traceFold {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs : List ℕ) (initial : Option (RestartCursor n)) : Option (RestartCursor n) :=
  (Arlib.Computation.Charged.foldl (fun acc _ => match acc with
    | none => pure none
    | some current => traceReturn r o₁ o₂ tape s q w current) xs initial).val

/-- INTERNAL: Aborted trace folds remain aborted. -/
theorem trace_fold_none {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (xs : List ℕ) : traceFold r o₁ o₂ tape s q w xs none = none := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    simpa only [traceFold, Arlib.Computation.Charged.val_foldl_cons,
      Arlib.Computation.Charged.val_pure] using ih

/-- INTERNAL: Split off one actual positive-time return, preserving its cursor. -/
theorem trace_fold_cons {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (a : ℕ) (xs : List ℕ) (current : RestartCursor n) :
    traceFold r o₁ o₂ tape s q w (a::xs) (some current) =
      ((traceReturn r o₁ o₂ tape s q w current).val).bind
        (fun next => traceFold r o₁ o₂ tape s q w xs (some next)) := by
  unfold traceFold
  rw [Arlib.Computation.Charged.val_foldl_cons]
  cases h : (traceReturn r o₁ o₂ tape s q w current).val with
  | none => exact trace_fold_none r o₁ o₂ tape s q w xs
  | some next => rfl

/-- INTERNAL: A successful trace fold replays exactly its consumed interval.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem trace_fold_success_interval {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (xs : List ℕ)
    (current : RestartCursor n) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => traceFold r o₁ o₂ tape s q w xs (some current))
      RestartCursor.bitCursor current.bitCursor := by
  apply ChainStepIntervalReplay.foldl_successReplay
  · intro tape a
    rfl
  · intro acc a
    exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s q w acc

/-- INTERNAL: Iterated covered actual returns are dominated by iterated ideal
returns, each of which is granted the full restart cap.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem covered_trace_fold_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (xs : List ℕ) (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length)
    (hvalid : (classifyState current.state).val ≠ .invalid) (target : PairedSet n) :
    fairMass head t (fun tape => ∃ out : RestartCursor n,
      out.bitCursor ≤ head.length+t ∧
      traceFold r o₁ o₂ tape s q w xs (some current) = some out ∧ out.state = target) ≤
      (iterate (returnWithin P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) s.restartCap) xs.length).entry
        current.state target := by
  classical
  let K := returnWithin P (Finset.univ.filter
    (fun x : PairedSet n => (classifyState x).val = .transversal)) s.restartCap
  induction xs generalizing head t current with
  | nil =>
    change _ ≤ if current.state = target then 1 else 0
    by_cases hs : current.state = target
    · simp only [hs, if_true]
      unfold fairMass
      calc
        _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ)^t := by
          apply Finset.sum_le_sum
          intro bits _
          split_ifs
          · exact le_rfl
          · positivity
        _ = 1 := by simp [card_vector]
    · simp only [hs, if_false]
      have he : ∀ tape, ¬ ∃ out : RestartCursor n,
          out.bitCursor ≤ head.length+t ∧
          traceFold r o₁ o₂ tape s q w [] (some current) = some out ∧ out.state = target := by
        intro tape
        rintro ⟨out, _, hr, ht⟩
        have heq : current = out := Option.some.inj hr
        exact hs (heq ▸ ht)
      simp only [fairMass, he, if_false, Finset.sum_const_zero, le_refl]
  | cons a xs ih =>
    let f := fun tape => (traceReturn r o₁ o₂ tape s q w current).val
    let E := fun tape (middle : RestartCursor n) => ∃ out : RestartCursor n,
      out.bitCursor ≤ head.length+t ∧
      traceFold r o₁ o₂ tape s q w xs (some middle) = some out ∧ out.state = target
    have hevent : ∀ bits : List.Vector Bool t,
        (∃ out : RestartCursor n, out.bitCursor ≤ head.length+t ∧
          traceFold r o₁ o₂ (finiteTape (head ++ bits.val)) s q w (a::xs) (some current) =
            some out ∧ out.state = target) →
        ∃ middle, f (finiteTape (head ++ bits.val)) = some middle ∧
          E (finiteTape (head ++ bits.val)) middle := by
      intro bits
      rintro ⟨out, hc, hr, ht⟩
      rw [trace_fold_cons] at hr
      obtain ⟨middle, hm, htail⟩ := Option.bind_eq_some_iff.mp hr
      exact ⟨middle, hm, out, hc, htail, ht⟩
    have hf : ChainStepIntervalReplay.SuccessReplay f RestartCursor.bitCursor head.length := by
      rw [← hcursor]
      exact TraceReturnIntervalReplay.traceReturn_success_interval r o₁ o₂ s q w current
    have hbound := FiniteStoppedKernelBind.stopped_kernel_bind_covered_bound
      head t f RestartCursor.bitCursor RestartCursor.state hf E
      (fun x => (iterate K xs.length).entry x target)
      (fun x => (iterate K xs.length).nonneg x target) (by
        intro bits middle _ hE
        obtain ⟨out, hc, hr, _⟩ := hE
        exact (trace_fold_success_interval r o₁ o₂ s q w xs middle _ out hr).1.trans hc)
      (by
        intro middle hstart hstop pref hm
        have hlen : (head ++ pref.val).length = middle.bitCursor := by
          simp only [List.length_append, pref.2]
          omega
        have hbudget : (head ++ pref.val).length + (t-(middle.bitCursor-head.length)) =
            head.length+t := by rw [hlen]; omega
        have hv : (classifyState middle.state).val ≠ .invalid := by
          have ht := RestartPhaseTransversal.traceReturn_transversal r o₁ o₂
            (finiteTape (head ++ pref.val)) s q w current middle hm
          rw [ht]
          intro h
          cases h
        have hi := ih (head ++ pref.val) (t-(middle.bitCursor-head.length)) middle
          hlen.symm hv
        have heq : fairMass (head ++ pref.val) (t-(middle.bitCursor-head.length))
            (fun tape => E tape middle) =
            fairMass (head ++ pref.val) (t-(middle.bitCursor-head.length)) (fun tape =>
              ∃ out : RestartCursor n,
                out.bitCursor ≤ (head ++ pref.val).length + (t-(middle.bitCursor-head.length)) ∧
                traceFold r o₁ o₂ tape s q w xs (some middle) = some out ∧ out.state = target) := by
          unfold fairMass
          apply Finset.sum_congr rfl
          intro bits _
          simp only [E, hbudget]
        rw [heq]
        exact hi)
    calc
      _ ≤ fairMass head t (fun tape => ∃ middle, f tape = some middle ∧ E tape middle) :=
        fairMass_mono head t _ _ hevent
      _ ≤ ∑ x : PairedSet n, fairMass head t (fun tape => ∃ middle, f tape = some middle ∧
          middle.bitCursor ≤ head.length+t ∧ middle.state = x) *
          (iterate K xs.length).entry x target := hbound
      _ ≤ ∑ x : PairedSet n, K.entry current.state x * (iterate K xs.length).entry x target := by
        apply Finset.sum_le_sum
        intro x _
        apply mul_le_mul_of_nonneg_right _ ((iterate K xs.length).nonneg x target)
        have hb := CappedTraceReturnSubkernel.covered_trace_return_bound r o₁ o₂ s q w P hstep
          head t current hcursor hvalid x
        have heq : fairMass head t (fun tape => ∃ middle, f tape = some middle ∧
            middle.bitCursor ≤ head.length+t ∧ middle.state = x) =
            fairMass head t (fun tape => ∃ out : RestartCursor n,
              out.bitCursor ≤ head.length+t ∧
              (traceReturn r o₁ o₂ tape s q w current).val = some out ∧ out.state = x) := by
          unfold fairMass
          apply Finset.sum_congr rfl
          intro bits _
          congr 1
          exact propext (by
            constructor <;> rintro ⟨out, h₁, h₂, h₃⟩ <;> exact ⟨out,h₂,h₁,h₃⟩)
        rw [heq]
        exact hb
      _ = _ := rfl

end CountingMatroid.Analysis.CappedTraceIterationSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · absorbing-option return folds replay consumed intervals and are dominated by ideal return iteration while preserving shared attempts and abort mass.
-/
