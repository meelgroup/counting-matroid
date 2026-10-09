import CountingMatroid.Analysis.SuccessfulPrefixCursor
import CountingMatroid.Analysis.BoundedUniformAbortMass

set_option autoImplicit false

/-!
Value-preserving restart instrumentation. The auxiliary natural number counts
only calls to `chainStep`; it survives both draw aborts and attempt-cap aborts.
It uses the original charged operations and the original tape. It establishes
no probabilistic bound and constructs no draw histories.
-/
namespace CountingMatroid.Analysis.RestartAttemptAccounting

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: The body of the actual positive-time return loop, factored out
without changing any of its guards or abort branches.
TEXLINE: main.tex:1163-1176 -/
def traceBody {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (acc : Option (RestartCursor n) × Bool) :
    Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) := do
  if acc.2 then pure none
  else match acc.1 with
  | none => pure none
  | some current =>
      let allowed ← lessThan current.attempts s.restartCap
      if allowed then
        let attempted ← chainStep r o₁ o₂ tape s.drawTrials q w
          current.state current.bitCursor
        let attempts ← successor current.attempts
        match attempted with
        | none => pure (some (none, true))
        | some (state, bitCursor) =>
            let kind ← classifyState state
            let returned ← match kind with
              | .transversal => pure true
              | _ => pure false
            pure (some (some ⟨state, bitCursor, attempts⟩, returned))
      else pure (some (none, true))

/-- INTERNAL: Exactly one attempt is made when the return-loop guard allows
`chainStep`; neither an absorbing state nor a refused guard spends a token. -/
def attemptIncrement {n : ℕ} (s : AnnealingSchedule)
    (acc : Option (RestartCursor n) × Bool) : ℕ :=
  if acc.2 then 0 else match acc.1 with
  | none => 0
  | some current => if current.attempts < s.restartCap then 1 else 0

/-- INTERNAL: Attach the attempt token to the original return-body result,
including the `some (none, true)` result on a draw abort. -/
def countedBody {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    Arlib.Computation.Charged Op Cell
      (Option ((Option (RestartCursor n) × Bool) × ℕ)) := do
  let next ← traceBody r o₁ o₂ tape s q w acc.1
  pure (next.map (fun result => (result, acc.2 + attemptIncrement s acc.1)))

/-- INTERNAL: Forgetting an auxiliary counter commutes with an early-break
loop whose lifted body preserves exactly the original continuation result. -/
private theorem while_projection {α β γ : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (g : (β × γ) → α → Arlib.Computation.Charged Op Cell (Option (β × γ)))
    (h : ∀ b c a, (g (b, c) a).val.map Prod.fst = (f b a).val)
    (xs : List α) (b : β) (c : γ) :
    (Arlib.Computation.Charged.foldlWhile g xs (b,c)).val.1 =
      (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b c with
  | nil => rfl
  | cons a xs ih =>
      have hp := h b c a
      cases hg : (g (b,c) a).val with
      | none =>
          have hf : (f b a).val = none := by simpa only [hg, Option.map_none] using hp.symm
          simp only [Arlib.Computation.Charged.val] at hg hf ⊢
          simp only [Arlib.Computation.Charged.foldlWhile, hg, hf]
      | some next =>
          have hf : (f b a).val = some next.1 := by
            simpa only [hg, Option.map_some] using hp.symm
          have hi := ih next.1 next.2
          simp only [Arlib.Computation.Charged.val] at hg hf hi ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, hg, hf] using hi

/-- INTERNAL: A positive-time trace return with its stopped global attempt
count, retained even when the public result is `none`.
TEXLINE: main.tex:1163-1176 -/
def countedReturn {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : RestartCursor n) (count : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n) × ℕ) := do
  let scan ← Arlib.Computation.Charged.repeatWhile
    (fun _ acc => countedBody r o₁ o₂ tape s q w acc) s.restartCap
    ((some start, false), count)
  pure ((if scan.1.2 then scan.1.1 else none), scan.2)

/-- INTERNAL: Evaluate a conditional charged result before comparing loop values. -/
private theorem conditional_value {α : Type} (P : Prop) [Decidable P]
    (a b : Arlib.Computation.Charged Op Cell α) :
    (if P then a else b).val = if P then a.val else b.val := by
  split_ifs <;> rfl

/-- INTERNAL: The instrumented return projects to the exact public return,
including draw abort, refused guard, and horizon exhaustion. -/
theorem countedReturn_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : RestartCursor n) (count : ℕ) :
    (countedReturn r o₁ o₂ tape s q w start count).val.1 =
      (traceReturn r o₁ o₂ tape s q w start).val := by
  have hp := while_projection (fun acc (_ : ℕ) => traceBody r o₁ o₂ tape s q w acc)
    (fun acc (_ : ℕ) => countedBody r o₁ o₂ tape s q w acc)
    (by
      intro b c a
      simp only [countedBody, Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_pure, Option.map_map]
      cases (traceBody r o₁ o₂ tape s q w b).val <;> rfl)
    (List.range s.restartCap) (some start, false) count
  let counted := (Arlib.Computation.Charged.repeatWhile
    (fun _ acc => countedBody r o₁ o₂ tape s q w acc) s.restartCap
    ((some start, false), count)).val
  let original := (Arlib.Computation.Charged.repeatWhile
    (fun _ acc => traceBody r o₁ o₂ tape s q w acc) s.restartCap
    (some start, false)).val
  change counted.1 = original at hp
  change (if counted.1.2 then counted.1.1 else none) =
    (if original.2 then (pure original.1 : Arlib.Computation.Charged Op Cell _)
      else pure none).val
  rw [← hp]
  split_ifs <;> rfl

/-- INTERNAL: Forgetting an auxiliary counter also commutes with a fixed loop. -/
private theorem fold_projection {α β γ : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (g : (β × γ) → α → Arlib.Computation.Charged Op Cell (β × γ))
    (h : ∀ b c a, (g (b,c) a).val.1 = (f b a).val)
    (xs : List α) (b : β) (c : γ) :
    (Arlib.Computation.Charged.foldl g xs (b,c)).val.1 =
      (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b c with
  | nil => rfl
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_cons]
      have hi := ih (g (b,c) a).val.1 (g (b,c) a).val.2
      rw [← h b c a]
      exact hi

/-- INTERNAL: One instrumented trace transition, preserving the absorbing
abort state and its last attempt count. -/
def countedTransition {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (acc : Option (RestartCursor n) × ℕ) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n) × ℕ) :=
  match acc.1 with
  | none => pure acc
  | some current => countedReturn r o₁ o₂ tape s q w current acc.2

/-- INTERNAL: One stored-parameter stage with retained abort accounting. -/
def countedStage {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (index : ℕ) (acc : Option (RestartCursor n) × ℕ) :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n) × ℕ) := do
  let a ← successor index
  let q ← ratPower s.ρ a
  let w ← learnedWeightRead tables a s.L
  Arlib.Computation.Charged.repeatFor
    (fun _ acc => countedTransition r o₁ o₂ tape s q w acc) s.τ acc

/-- INTERNAL: Restart instrumentation with the same fresh transversal, tape,
stored tables, stage order and shared cap as the program.
TEXLINE: main.tex:1163-1176 -/
def countedRestart {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ) × ℕ) := do
  let initial ← freshTransversal n tape cursor
  let result ← Arlib.Computation.Charged.repeatFor
    (fun index acc => countedStage r o₁ o₂ tape s tables index acc)
    j (some ⟨initial.1, initial.2, 0⟩, 0)
  pure (result.1.map (fun current => (current.state, current.bitCursor)), result.2)

/-- INTERNAL: Stage instrumentation projects to the original nested trace loop. -/
private theorem stage_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (index : ℕ) (acc : Option (RestartCursor n)) (count : ℕ) :
    (countedStage r o₁ o₂ tape s tables index (acc,count)).val.1 =
    (do match acc with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let w ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ acc => do
            match acc with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q w current)
            s.τ (some current) :
        Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val := by
  have hp (q : ℚ) (w : Multipliers n) := fold_projection
    (fun acc (_ : ℕ) => match acc with
      | none => pure none
      | some current => traceReturn r o₁ o₂ tape s q w current)
    (fun acc (_ : ℕ) => countedTransition r o₁ o₂ tape s q w acc)
    (by intro b c a; cases b <;> simp only [countedTransition,
      Arlib.Computation.Charged.val_pure, countedReturn_projection])
    (List.range s.τ) acc count
  cases acc <;> simp only [countedStage, Arlib.Computation.Charged.val_bind,
    successor, ratPower, learnedWeightRead, Arlib.Computation.Charged.val_op,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor, hp]
  · have hz (xs : List ℕ) :
        (Arlib.Computation.Charged.foldl (fun (acc : Option (RestartCursor n)) (_ : ℕ) =>
          match acc with
          | none => pure none
          | some current => traceReturn r o₁ o₂ tape s
              (ratPower s.ρ (index + 1)).val
              (learnedWeightRead tables (index + 1) s.L).val current) xs none).val = none := by
        induction xs with
        | nil => rfl
        | cons a xs ih => simpa only [Arlib.Computation.Charged.val_foldl_cons,
            Arlib.Computation.Charged.val_pure] using ih
    exact hz (List.range s.τ)

/-- INTERNAL: The complete counted restart has exactly the original result.
The additional count, unlike `RestartCursor.attempts`, survives an abort. -/
theorem countedRestart_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    (countedRestart r o₁ o₂ tape s tables j cursor).val.1 =
      (restartPhase r o₁ o₂ tape s tables j cursor).val := by
  have hp := fold_projection
    (fun acc index => do match acc with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let w ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ acc => do
            match acc with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q w current)
            s.τ (some current))
    (fun acc index => countedStage r o₁ o₂ tape s tables index acc)
    (fun b c a => stage_projection r o₁ o₂ tape s tables a b c)
    (List.range j)
    (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩) 0
  simp only [countedRestart, restartPhase, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
  rw [hp]
  simp only [Arlib.Computation.Charged.repeatFor] at hp ⊢
  -- Keep the entire original stage fold as a single expression in the case split.
  generalize he : (Arlib.Computation.Charged.foldl
    (fun acc index => do match acc with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let w ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.foldl (fun acc (_ : ℕ) => do
            match acc with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q w current)
            (List.range s.τ) (some current)) (List.range j)
    (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩)).val = result
  cases result <;> rfl

/-- INTERNAL: The already-proved actual-history data fixing one restart's
stored kernels and starting bit cursor. This record asserts no moment bound
and no equality between the cursor and the truncated prefix length.
TEXLINE: main.tex:1207-1212 -/
structure RestartPrefixWitness (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ) (pref : List Bool) where
  bits : List Bool
  current : AnnealingCursor n
  length : bits.length = CountingMatroid.Model.Run.blockLength n r p
  previous : ∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
    (fun i => (bits[i]?).getD false) (CountingMatroid.Interface.Pseudocode.setup n p) a
  reached : BoundedRunPhaseHistory.phaseHistory r o₁ o₂
    (fun i => (bits[i]?).getD false) (CountingMatroid.Interface.Pseudocode.setup n p) j =
      some current
  good : FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂
    (CountingMatroid.Interface.Pseudocode.setup n p) j current
  consumed : pref = bits.take current.bitCursor

/-- INTERNAL: Package the existing successful-prefix extraction without
assuming the unproved operational cost or draw cover. -/
theorem successful_prefix_witness (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (j : ℕ)
    (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool)
    (hprefix : PhaseObservationExperiment.SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    Nonempty (RestartPrefixWitness n r o₁ o₂ p j pref) := by
  obtain ⟨bits, current, hlen, hprevious, hhistory, hstored, hpref, _⟩ :=
    SuccessfulPrefixAbortBound.successful_prefix_has_good_cursor
      n r o₁ o₂ p j hj pref hprefix
  exact ⟨⟨bits, current, hlen, hprevious, hhistory, hstored, hpref⟩⟩

/-- INTERNAL: The fixed stopped cost for a restart after this actual earlier
history, evaluated on the original finite tape. Draw aborts retain the token
spent on their last attempted transition; no constant cap witness is used.
TEXLINE: main.tex:1230-1239,1392-1421 -/
noncomputable def prefixAttemptCost {n r : ℕ} {o₁ o₂ : IndependenceOracle n}
    {p : InputParams} {j : ℕ} {pref : List Bool}
    (history : RestartPrefixWitness n r o₁ o₂ p j pref) (suffix : List Bool) : ℕ :=
  (countedRestart r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
    (CountingMatroid.Interface.Pseudocode.setup n p) history.current.tables
    j history.current.bitCursor).val.2

end CountingMatroid.Analysis.RestartAttemptAccounting

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · instrumented the actual guarded trace body and nested restart; projection preserves every public value, while the independent attempt counter survives abort. Packaged the existing reached-prefix witness.
-/
