import CountingMatroid.Analysis.RestartAttemptAccounting
import CountingMatroid.Analysis.CappedTraceReturnSubkernel
import CountingMatroid.Analysis.StationaryReturnOccupation

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The number of `chainStep` attempts made by one actual positive-time return,
as a value recursion. The instrumented return adds exactly this number to its
retained counter, including the attempt that ends in a draw abort. On a fresh
finite suffix whose every attempted step stays inside the block, the chance of
making more than m attempts is at most the ideal positive-time survival tail.
-/
namespace CountingMatroid.Analysis.ReturnAttemptTail

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.PositiveTimeTraceKernel
open CountingMatroid.Analysis.RestartAttemptAccounting
open Arlib.Probability Arlib.MarkovChains

/-- INTERNAL: Attempts made by a capped positive-time return scan: one for
every permitted guard, including an attempt whose draw aborts.
TEXLINE: main.tex:1163-1176 -/
noncomputable def attemptScan {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) :
    ℕ → RestartCursor n → ℕ
  | 0, _ => 0
  | k + 1, current =>
      if current.attempts < s.restartCap then
        1 + match (chainStep r o₁ o₂ tape s.drawTrials q w current.state
            current.bitCursor).val with
          | none => 0
          | some step =>
              if (classifyState step.1).val = .transversal then 0
              else attemptScan r o₁ o₂ tape s q w k ⟨step.1, step.2, current.attempts + 1⟩
      else 0

/-- INTERNAL: A scan of horizon k makes at most k attempts. -/
theorem attempt_scan_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (k : ℕ) (current : RestartCursor n) :
    attemptScan r o₁ o₂ tape s q w k current ≤ k := by
  induction k generalizing current with
  | zero => exact le_rfl
  | succ k ih =>
      simp only [attemptScan]
      split_ifs with ha
      · split
        · omega
        · rename_i step _
          split_ifs
          · omega
          · have := ih ⟨step.1, step.2, current.attempts + 1⟩
            omega
      · omega

/-- INTERNAL: Expose the value recursion of a charged early-break fold. -/
private theorem foldlWhile_cons_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell (Option β))
    (a : α) (xs : List α) (b : β) :
    (Arlib.Computation.Charged.foldlWhile f (a :: xs) b).val =
      match (f b a).val with
      | none => b
      | some next => (Arlib.Computation.Charged.foldlWhile f xs next).val := by
  cases h : (f b a).val <;>
    simp only [Arlib.Computation.Charged.val] at h ⊢ <;>
    simp [Arlib.Computation.Charged.foldlWhile, h]

/-- INTERNAL: The instrumented return adds exactly the scan's attempts to its
retained counter, whatever the outcome.
TEXLINE: main.tex:1163-1176 -/
theorem counted_return_count {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : RestartCursor n) (count : ℕ) :
    (countedReturn r o₁ o₂ tape s q w start count).val.2 =
      count + attemptScan r o₁ o₂ tape s q w s.restartCap start := by
  let body := fun (acc : (Option (RestartCursor n) × Bool) × ℕ) (_ : ℕ) =>
    countedBody r o₁ o₂ tape s q w acc
  let scan := fun xs acc => (Arlib.Computation.Charged.foldlWhile body xs acc).val
  have hstopped (xs : List ℕ) (acc : Option (RestartCursor n)) (c : ℕ) :
      scan xs ((acc, true), c) = ((acc, true), c) := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      rw [show scan (a::xs) ((acc,true),c) = _ from foldlWhile_cons_value _ _ _ _]
      rfl
  have hnone (xs : List ℕ) (c : ℕ) :
      scan xs ((none, false), c) = ((none, false), c) := by
    cases xs with
    | nil => rfl
    | cons a xs =>
      rw [show scan (a::xs) ((none,false),c) = _ from foldlWhile_cons_value _ _ _ _]
      rfl
  have hrec : ∀ (xs : List ℕ) (current : RestartCursor n) (c : ℕ),
      (scan xs ((some current, false), c)).2 =
        c + attemptScan r o₁ o₂ tape s q w xs.length current := by
    intro xs
    induction xs with
    | nil => intro current c; rfl
    | cons a xs ih =>
      intro current c
      have hvalue : scan (a::xs) ((some current, false), c) =
          match (body ((some current, false), c) a).val with
          | none => ((some current, false), c)
          | some next => scan xs next := by
        dsimp only [scan]
        rw [foldlWhile_cons_value]
        cases (body ((some current, false), c) a).val <;> rfl
      rw [hvalue]
      simp only [body, countedBody, traceBody, attemptIncrement, Bool.false_eq_true,
        if_false, Arlib.Computation.Charged.val_bind, Model.Operations.lessThan,
        Arlib.Computation.Charged.val_op, List.length_cons, attemptScan,
        decide_eq_true_eq, Arlib.Computation.Charged.val_pure]
      by_cases ha : current.attempts < s.restartCap
      · simp only [ha, if_true, Arlib.Computation.Charged.val_bind]
        cases hs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
            current.bitCursor).val with
        | none =>
            simp only [Arlib.Computation.Charged.val_pure, Option.map_some, hstopped]
        | some step =>
          simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
            Arlib.Computation.Charged.val_op]
          cases step with
          | mk state stop =>
            cases hk : (classifyState state).val <;>
              simp only [hk, Arlib.Computation.Charged.val_bind,
                Arlib.Computation.Charged.val_pure, Option.map_some, reduceCtorEq,
                if_true, if_false]
            · simp only [hstopped]
            · rw [ih]; omega
            · rw [ih]; omega
      · simp only [ha, if_false, Arlib.Computation.Charged.val_pure, Option.map_some,
          hstopped]
  unfold countedReturn
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.repeatWhile]
  have h := hrec (List.range s.restartCap) start count
  simp only [List.length_range] at h
  exact h

/-- INTERNAL: The paper's positive-time occupation summands: the first
attempt always occurs, and attempt m+1 needs m+1 off-target steps.
TEXLINE: main.tex:1072-1087 -/
noncomputable def tailWeight {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) : ℕ → Ω → ℝ
  | 0 => fun _ => 1
  | m + 1 => fun x => ∑ z, P x z * survive P A m z

/-- INTERNAL: Tail weights are nonnegative. -/
theorem tailWeight_nonneg {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) (m : ℕ) (x : Ω) : 0 ≤ tailWeight P A m x := by
  cases m with
  | zero => simp [tailWeight]
  | succ m =>
      exact Finset.sum_nonneg fun z _ => mul_nonneg (P.coe_nonneg x z) (survive_nonneg P A m z)

/-- INTERNAL: Off the target, positive-time survival is the tail weight. -/
theorem survive_eq_tailWeight {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) (m : ℕ) (x : Ω) (hx : x ∉ A) :
    survive P A m x = tailWeight P A m x := by
  cases m with
  | zero => simp [tailWeight, hx]
  | succ m => rw [survive_succ_apply, if_neg hx]; rfl

/-- INTERNAL: The finite occupation budget, as tail weights summed against
the stationary law restricted to the target.
TEXLINE: main.tex:1072-1087 -/
theorem return_occupation_eq_tail_sum {Ω : Type} [Fintype Ω] [DecidableEq Ω]
    (P : FinChain Ω) (A : Finset Ω) (μ : FinDist Ω) (H : ℕ) :
    StationaryReturnOccupation.returnOccupation P A μ H =
      ∑ x, (if x ∈ A then μ x else 0) *
        ∑ m ∈ Finset.range (H + 1), tailWeight P A m x := by
  unfold StationaryReturnOccupation.returnOccupation
  have h1 : (∑ x ∈ A, μ x) = ∑ x, (if x ∈ A then μ x else 0) := by
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  have h2 : ∀ x, (if x ∈ A then μ x else 0) *
      ∑ m ∈ Finset.range (H + 1), tailWeight P A m x =
      (if x ∈ A then μ x else 0) + ∑ k ∈ Finset.range H,
        (if x ∈ A then μ x * (∑ z, P x z * survive P A k z) else 0) := by
    intro x
    rw [Finset.sum_range_succ', mul_add, Finset.mul_sum]
    by_cases hx : x ∈ A <;> simp [hx, tailWeight, add_comm]
  simp_rw [h2, Finset.sum_add_distrib]
  rw [h1, Finset.sum_comm]

/-- INTERNAL: Event mass on a fresh finite suffix is at most one. -/
theorem fairMass_le_one (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) :
    fairMass head t E ≤ 1 := by
  classical
  unfold fairMass
  calc
    _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ)^t := by
      apply Finset.sum_le_sum
      intro bits _
      split_ifs
      · exact le_rfl
      · positivity
    _ = 1 := by simp [card_vector]

/-- INTERNAL: On a fresh finite suffix, a return whose attempted steps all stay
in the block makes more than m attempts with at most the ideal tail weight.
The invariant carries the deterministic bit budget between attempts.
TEXLINE: main.tex:1072-1087,1163-1176,1392-1421 -/
theorem attempt_scan_tail {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (P : FinChain (PairedSet n))
    (hstep : ∀ (head : List Bool) (t : ℕ) (x y : PairedSet n),
      (classifyState x).val ≠ .invalid →
      fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape s.drawTrials q w x head.length).val = some (y, stop)) ≤ P x y)
    (Inv : RestartCursor n → Prop) (lim : ℕ)
    (hinv : ∀ (tape : ℕ → Bool) (current : RestartCursor n) (y : PairedSet n) (stop : ℕ),
      Inv current → current.attempts < s.restartCap →
      (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
        some (y, stop) →
      stop ≤ lim ∧ Inv ⟨y, stop, current.attempts + 1⟩)
    (k m : ℕ) (head : List Bool) (t : ℕ) (current : RestartCursor n)
    (hcursor : current.bitCursor = head.length) (hlim : head.length + t = lim)
    (hvalid : (classifyState current.state).val ≠ .invalid) (hcur : Inv current) :
    fairMass head t (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w k current) ≤
      tailWeight P (Finset.univ.filter
        (fun x => (classifyState x).val = .transversal)) m current.state := by
  classical
  let A := Finset.univ.filter (fun x : PairedSet n => (classifyState x).val = .transversal)
  induction k generalizing m head t current with
  | zero =>
      have hz : fairMass head t
          (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w 0 current) = 0 := by
        simp [fairMass, attemptScan]
      rw [hz]
      exact tailWeight_nonneg P A m current.state
  | succ k ih =>
    by_cases ha : current.attempts < s.restartCap
    · cases m with
      | zero => exact (fairMass_le_one _ _ _).trans_eq rfl
      | succ m =>
        let f := fun tape => (chainStep r o₁ o₂ tape s.drawTrials q w
          current.state head.length).val
        let E := fun tape (a : PairedSet n) (stop : ℕ) =>
          (classifyState a).val ≠ .transversal ∧
            m + 1 ≤ attemptScan r o₁ o₂ tape s q w k ⟨a, stop, current.attempts + 1⟩
        have hevent : ∀ bits : List.Vector Bool t,
            m + 1 + 1 ≤ attemptScan r o₁ o₂ (finiteTape (head ++ bits.val)) s q w (k+1)
              current →
            ∃ a, ∃ stop, stop ≤ head.length+t ∧
              f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
              E (finiteTape (head ++ bits.val)) a stop := by
          intro bits h
          simp only [attemptScan, ha, if_true, hcursor] at h
          cases hf : (chainStep r o₁ o₂ (finiteTape (head ++ bits.val)) s.drawTrials q w
              current.state head.length).val with
          | none => simp only [hf] at h; omega
          | some step =>
              simp only [hf] at h
              by_cases ht : (classifyState step.1).val = .transversal
              · simp only [ht, if_true] at h; omega
              · simp only [ht, if_false] at h
                have hb := hinv (finiteTape (head ++ bits.val)) current step.1 step.2 hcur ha
                  (by rw [hcursor]; exact hf)
                exact ⟨step.1, step.2, by omega, hf, ht, by omega⟩
        have hsum : fairMass head t
            (fun tape => m + 1 + 1 ≤ attemptScan r o₁ o₂ tape s q w (k+1) current) ≤
            ∑ a : PairedSet n, fairMass head t (fun tape => ∃ stop,
              stop ≤ head.length+t ∧ f tape = some (a,stop) ∧ E tape a stop) := by
          unfold fairMass
          rw [Finset.sum_comm]
          apply Finset.sum_le_sum
          intro bits _
          dsimp only
          split_ifs with h
          · obtain ⟨a, hs⟩ := hevent bits h
            apply le_trans (show (1 / (2 : ℝ)^t) ≤
              (if ∃ stop, stop ≤ head.length+t ∧
                f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
                E (finiteTape (head ++ bits.val)) a stop then 1 / (2 : ℝ)^t else 0) by
                  rw [if_pos hs])
            convert (Finset.single_le_sum (f := fun a =>
              if ∃ stop, stop ≤ head.length+t ∧
                f (finiteTape (head ++ bits.val)) = some (a,stop) ∧
                E (finiteTape (head ++ bits.val)) a stop then 1 / (2 : ℝ)^t else 0)
              (fun _ _ => by split_ifs <;> positivity) (Finset.mem_univ a)) using 1
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> rfl
          · exact Finset.sum_nonneg (fun _ _ => by split_ifs <;> positivity)
        apply hsum.trans
        change _ ≤ ∑ a : PairedSet n, P current.state a * survive P A m a
        apply Finset.sum_le_sum
        intro a _
        have hbound := FiniteStoppedFiberMass.stopped_next_bound head t f
          (ChainStepIntervalReplay.chainStep_success_interval r o₁ o₂ s.drawTrials q w
            current.state head.length) a (fun tape stop => E tape a stop)
          (survive P A m a) (survive_nonneg P A m a) (by
            intro stop hstart hstop pref hf
            have hpref : (head ++ pref.val).length = stop := by
              simp only [List.length_append, pref.2]
              omega
            by_cases ht : (classifyState a).val = .transversal
            · have hnone : ∀ tape, ¬ E tape a stop := fun tape h => h.1 ht
              simp only [fairMass, hnone, if_false, Finset.sum_const_zero]
              exact survive_nonneg P A m a
            · have hA : a ∉ A := by simp [A, ht]
              have hv := ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ _ s.drawTrials
                q w current.state head.length (a,stop) hvalid hf
              have hb := hinv (finiteTape (head ++ pref.val)) current a stop hcur ha
                (by rw [hcursor]; exact hf)
              have hi := ih m (head ++ pref.val) (t-(stop-head.length))
                ⟨a,stop,current.attempts+1⟩ hpref.symm (by rw [hpref]; omega) hv hb.2
              rw [survive_eq_tailWeight P A m a hA]
              refine le_trans (FiniteStoppedFiberMass.fairMass_mono _ _ _ _ ?_) hi
              intro bits h
              exact h.2)
        exact hbound.trans (mul_le_mul_of_nonneg_right
          (by simpa only [hcursor] using hstep head t current.state a hvalid)
          (survive_nonneg P A m a))
    · have hz : fairMass head t
          (fun tape => m + 1 ≤ attemptScan r o₁ o₂ tape s q w (k+1) current) = 0 := by
        simp [fairMass, attemptScan, ha]
      rw [hz]
      exact tailWeight_nonneg P A m current.state

end CountingMatroid.Analysis.ReturnAttemptTail

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · created · per-return attempt recursion, exact retained-count identity for the instrumented return, occupation budget as tail sums, and the covered attempt-tail bound.
-/
