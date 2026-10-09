import CountingMatroid.Analysis.RestartAttemptAccounting
import CountingMatroid.Analysis.ChainDrawSiteReplay

set_option autoImplicit false

/-!
A concrete ordinal pre-draw probe for the counted restart. The probe observes
an allowed chain attempt before its trials and retains its first descriptor,
including when the ensuing attempt aborts. Forgetting the descriptor preserves
both components of the counted restart, not just its public result.
No stopping law, finite-block bound, or abort attribution is asserted here.
-/
namespace CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Lift a fixed fold through a value-preserving observer. -/
theorem fold_observer_projection {α β γ : Type}
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

/-- INTERNAL: Lift an early-break fold through a value-preserving observer;
the observer cannot turn a stopped body into a continuing one. -/
theorem while_observer_projection {α β γ : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (g : (β × γ) → α → Arlib.Computation.Charged Op Cell (Option (β × γ)))
    (h : ∀ b c a, (g (b,c) a).val.map Prod.fst = (f b a).val)
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

/-- INTERNAL: Inspect exactly the selected ordinal attempt before invoking
its counted body. The retained counter fixes the ordinal even on aborts.
TEXLINE: main.tex:1163-1176,1392-1421 -/
noncomputable def bodySite {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    Option (ℕ × ℕ) :=
  if acc.1.2 then none else
  match acc.1.1 with
  | none => none
  | some current =>
    if current.attempts < s.restartCap ∧ acc.2 = ordinal then
      chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw
    else none

/-- INTERNAL: Sticky pre-draw recording around the original counted body.
Computing a descriptor observes the tape without replacing its randomness. -/
noncomputable def probedBody {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      (Option (((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))) := do
  let observed := acc.2.or (bodySite r o₁ o₂ tape s q w ordinal draw acc.1)
  let next ← countedBody r o₁ o₂ tape s q w acc.1
  pure (next.map (fun result => (result, observed)))

/-- INTERNAL: Probing preserves the exact body continuation and count. -/
theorem probedBody_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × Bool) × ℕ) (observed : Option (ℕ × ℕ)) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (acc, observed)).val.map Prod.fst =
      (countedBody r o₁ o₂ tape s q w acc).val := by
  simp only [probedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Option.map_map]
  cases (countedBody r o₁ o₂ tape s q w acc).val <;> rfl

/-- INTERNAL: Run the actual capped return scan while retaining a descriptor. -/
noncomputable def probedReturn {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (observed : Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      ((Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) := do
  let scan ← Arlib.Computation.Charged.repeatWhile
    (fun _ acc => probedBody r o₁ o₂ tape s q w ordinal draw acc) s.restartCap
    (((some start, false), count), observed)
  pure (((if scan.1.1.2 then scan.1.1.1 else none), scan.1.2), scan.2)

/-- INTERNAL: Forgetting the probe preserves return failure and retained cost. -/
theorem probedReturn_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.1 =
      (countedReturn r o₁ o₂ tape s q w start count).val := by
  have hp := while_observer_projection
    (fun acc (_ : ℕ) => countedBody r o₁ o₂ tape s q w acc)
    (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
    (fun b c _ => probedBody_projection r o₁ o₂ tape s q w ordinal draw b c)
    (List.range s.restartCap) ((some start, false), count) observed
  simp only [probedReturn, countedReturn, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
  rw [hp]

/-- INTERNAL: Preserve the absorbing failure state between trace returns. -/
noncomputable def probedTransition {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      ((Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :=
  match acc.1.1 with
  | none => pure acc
  | some current => probedReturn r o₁ o₂ tape s q w ordinal draw current acc.1.2 acc.2

/-- INTERNAL: The transition observer preserves both counted components. -/
theorem probedTransition_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (acc : Option (RestartCursor n) × ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw (acc,observed)).val.1 =
      (countedTransition r o₁ o₂ tape s q w acc).val := by
  cases h : acc.1 <;> simp only [probedTransition, countedTransition, h,
    Arlib.Computation.Charged.val_pure, probedReturn_projection]

/-- INTERNAL: Observe the same stored kernel throughout a stage. -/
noncomputable def probedStage {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (ordinal : ℕ) (draw : Fin 3) (index : ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    Arlib.Computation.Charged Op Cell
      ((Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) := do
  let a ← successor index
  let q ← ratPower s.ρ a
  let w ← learnedWeightRead tables a s.L
  Arlib.Computation.Charged.repeatFor
    (fun _ acc => probedTransition r o₁ o₂ tape s q w ordinal draw acc) s.τ acc

/-- INTERNAL: The stage observer preserves result and cost with arbitrary
stored weights; no multiplier accuracy assumption enters this identity. -/
theorem probedStage_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (ordinal : ℕ) (draw : Fin 3) (index : ℕ) (acc : Option (RestartCursor n) × ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedStage r o₁ o₂ tape s tables ordinal draw index (acc,observed)).val.1 =
      (countedStage r o₁ o₂ tape s tables index acc).val := by
  simp only [probedStage, countedStage, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.repeatFor]
  exact fold_observer_projection _ _
    (fun b c _ => probedTransition_projection r o₁ o₂ tape s _ _ ordinal draw b c)
    _ acc observed

/-- INTERNAL: Probe one ordinal draw in the concrete counted restart.
The first recorded descriptor survives subsequent aborts and stages.
TEXLINE: main.tex:1163-1176,1392-1421 -/
noncomputable def probedRestart {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor ordinal : ℕ) (draw : Fin 3) :
    Arlib.Computation.Charged Op Cell
      ((Option (PairedSet n × ℕ) × ℕ) × Option (ℕ × ℕ)) := do
  let initial ← freshTransversal n tape cursor
  let result ← Arlib.Computation.Charged.repeatFor
    (fun index acc => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
    j ((some ⟨initial.1, initial.2, 0⟩, 0), none)
  pure ((result.1.1.map (fun current => (current.state, current.bitCursor)), result.1.2),
    result.2)

/-- INTERNAL: The complete probe is value preserving even on an abort.
Both the public result and the retained attempted-transition count agree. -/
theorem probed_restart_projection {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor ordinal : ℕ) (draw : Fin 3) :
    (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.1 =
      (countedRestart r o₁ o₂ tape s tables j cursor).val := by
  have hp := fold_observer_projection
    (fun acc index => countedStage r o₁ o₂ tape s tables index acc)
    (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
    (fun b c index => probedStage_projection r o₁ o₂ tape s tables ordinal draw index b c)
    (List.range j)
    (some ⟨(freshTransversal n tape cursor).val.1,
      (freshTransversal n tape cursor).val.2, 0⟩, 0) none
  simp only [probedRestart, countedRestart, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
  rw [hp]

/-- INTERNAL: Absolute pre-draw cursor and denominator at ordinal `3*a+b`.
Unlike a finite suffix descriptor, this definition needs no block bound. -/
noncomputable def restartDrawProbe {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) (k : Fin (3 * s.restartCap)) : Option (ℕ × ℕ) :=
  (probedRestart r o₁ o₂ tape s tables j cursor (k.val / 3)
    ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩).val.2

/-- INTERNAL: Transfer a state invariant along a fixed charged fold. -/
private theorem fold_invariant {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (h : ∀ b a, P b → P (f b a).val) (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons]
    exact ih _ (h b a hb)

/-- INTERNAL: Early stopping retains the old invariant; continuing requires
it only for actual body results. -/
private theorem while_invariant {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (h : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
    cases hf : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at hf ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hb
    | some next =>
      have hn := ih next (h b a next hb hf)
      simp only [Arlib.Computation.Charged.val] at hf hn ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hf] using hn

/-- INTERNAL: A return scan cannot overwrite a descriptor captured before
that scan, irrespective of later tape bits or of a subsequent abort.
TEXLINE: main.tex:1392-1421 -/
theorem probed_return_retains {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (d : ℕ × ℕ) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count (some d)).val.2 = some d := by
  simp only [probedReturn, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
  apply while_invariant (fun acc => acc.2 = some d) _ ?_
    (List.range s.restartCap) (((some start, false), count), some d) rfl
  intro acc _ next ha he
  simp only [probedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Option.map_eq_some_iff] at he
  obtain ⟨result, _, he⟩ := he
  cases he
  simp only [ha, Option.some_or]

/-- INTERNAL: Positivity is an observation invariant independent of cursor
coverage and stopping-prefix replay. -/
private def PositiveObservation (observed : Option (ℕ × ℕ)) : Prop :=
  ∀ d, observed = some d → 0 < d.2

/-- INTERNAL: Every concrete ordinal restart probe has a positive denominator.
This proof needs no hypothesis about multiplier accuracy or tape coverage.
TEXLINE: main.tex:1392-1421 -/
theorem restartDrawProbe_positive {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) (k : Fin (3 * s.restartCap)) (d : ℕ × ℕ) (hn : 0 < n)
    (hs : restartDrawProbe r o₁ o₂ tape s tables j cursor k = some d) : 0 < d.2 := by
  have hsite (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (acc : (Option (RestartCursor n) × Bool) × ℕ) :
      PositiveObservation (bodySite r o₁ o₂ tape s q w ordinal draw acc) := by
    intro out hout
    unfold bodySite at hout
    split at hout
    · cases hout
    · cases hc : acc.1.1 with
      | none => simp only [hc] at hout; cases hout
      | some current =>
        simp only [hc] at hout
        split at hout
        · exact chainDrawSite_positive r o₁ o₂ tape s q w current.state
            current.bitCursor draw out hn hout
        · cases hout
  have hbody (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
      (next : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
      (ha : PositiveObservation acc.2)
      (he : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val = some next) :
      PositiveObservation next.2 := by
    have hp : PositiveObservation
        (acc.2.or (bodySite r o₁ o₂ tape s q w ordinal draw acc.1)) := by
      cases ho : acc.2 with
      | none => simpa only [ho, Option.or] using hsite q w ordinal draw acc.1
      | some old => simpa only [ho, Option.some_or] using ha
    simp only [probedBody, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Option.map_eq_some_iff] at he
    obtain ⟨result, _, he⟩ := he
    cases he
    exact hp
  have hreturn (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (start : RestartCursor n) (count : ℕ) (observed : Option (ℕ × ℕ))
      (ho : PositiveObservation observed) :
      PositiveObservation
        (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.2 := by
    cases he : observed with
    | none =>
      simp only [he] at ho
      simp only [probedReturn, Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatWhile]
      exact while_invariant (fun acc => PositiveObservation acc.2) _
        (fun b _ next hb he => hbody q w ordinal draw b next hb he)
        (List.range s.restartCap) (((some start, false), count), none) ho
    | some d =>
      simp only [he] at ho
      rw [probed_return_retains]
      exact ho
  have htransition (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3)
      (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
      (ho : PositiveObservation acc.2) :
      PositiveObservation (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.2 := by
    cases hc : acc.1.1 with
    | none => simpa only [probedTransition, hc, Arlib.Computation.Charged.val_pure] using ho
    | some current =>
      simpa only [probedTransition, hc] using
        hreturn q w ordinal draw current acc.1.2 acc.2 ho
  have hstage (ordinal : ℕ) (draw : Fin 3) (index : ℕ)
      (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
      (ho : PositiveObservation acc.2) :
      PositiveObservation (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.2 := by
    simp only [probedStage, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.repeatFor]
    exact fold_invariant (fun acc => PositiveObservation acc.2) _
      (fun b _ hb => htransition _ _ ordinal draw b hb) _ acc ho
  have hrestart (ordinal : ℕ) (draw : Fin 3) :
      PositiveObservation (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.2 := by
    simp only [probedRestart, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
    apply fold_invariant (fun acc => PositiveObservation acc.2) _
      (fun b index hb => hstage ordinal draw index b hb)
    intro out he
    cases he
  exact hrestart _ _ d hs

end CountingMatroid.Analysis.RestartDrawProbe

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · return scans retain already-captured descriptors independently of later tape; used this latch in denominator positivity.
* 2026-10-09 · proved · concrete sticky ordinal probes preserve the counted body,
  return, transition, stage, and complete restart, including the abort cost.
-/
