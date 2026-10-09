import CountingMatroid.Analysis.RestartPhaseIntervalReplay

set_option autoImplicit false

/-!
Every successful capped return ends in the transversal class. Consequently
successful restarts return a transversal, including phases with no crossed
levels or no trace transitions. These are deterministic operational facts;
they make no probability or finite-tape coverage claim.
-/

namespace CountingMatroid.Analysis.RestartPhaseTransversal

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: An early-break charged fold preserves an invariant when each
continuing step preserves it. -/
private theorem foldWhile_preserves {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (hstep : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      have hrec : (Arlib.Computation.Charged.foldlWhile f (a :: xs) b).val =
          match (f b a).val with
          | none => b
          | some next => (Arlib.Computation.Charged.foldlWhile f xs next).val := by
        cases h : (f b a).val <;>
          simp only [Arlib.Computation.Charged.val] at h ⊢ <;>
          simp [Arlib.Computation.Charged.foldlWhile, h]
      rw [hrec]
      cases h : (f b a).val with
      | none => exact hb
      | some next => exact ih next (hstep b a next hb h)

/-- INTERNAL: A successful positive-time return has actually reached the
transversal classifier branch, regardless of its initial state.
TEXLINE: main.tex:1163-1176 -/
theorem traceReturn_transversal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start result : RestartCursor n)
    (h : (traceReturn r o₁ o₂ tape s q weights start).val = some result) :
    (classifyState result.state).val = .transversal := by
  let P : Option (RestartCursor n) × Bool → Prop := fun acc =>
    ∀ current, acc.1 = some current → acc.2 = true →
      (classifyState current.state).val = .transversal
  let body : ℕ → (Option (RestartCursor n) × Bool) →
      Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) :=
    fun (_ : ℕ) (acc : Option (RestartCursor n) × Bool) => do
    if acc.2 then pure none
    else
      match acc.1 with
      | none => pure none
      | some current =>
          let allowed ← lessThan current.attempts s.restartCap
          if allowed then
            let attempted ← chainStep r o₁ o₂ tape s.drawTrials q weights
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
  have hstep : ∀ acc i next, P acc → (body i acc).val = some next → P next := by
    intro acc i next hp hn
    dsimp only [body] at hn
    split at hn
    · cases hn
    · split at hn
      · cases hn
      · simp only [Arlib.Computation.Charged.val_bind] at hn
        split at hn
        · simp only [Arlib.Computation.Charged.val_bind] at hn
          split at hn
          · have heq := Option.some.inj hn
            subst next
            intro current hc _
            cases hc
          · rename_i state cursor _
            simp only [Arlib.Computation.Charged.val_bind] at hn
            cases hk : (classifyState state).val <;>
              simp only [hk, Arlib.Computation.Charged.val_pure] at hn
            all_goals
              have heq := Option.some.inj hn
              subst next
              intro current hc hd
              have hcurrent := Option.some.inj hc
              subst current
            · exact hk
            · cases hd
            · cases hd
        · have heq := Option.some.inj hn
          subst next
          intro current hc _
          cases hc
  have hscan := foldWhile_preserves P (fun acc i => body i acc) hstep
    (List.range s.restartCap) (some start, false) (by
      intro current _ hd
      cases hd)
  unfold traceReturn at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatWhile] at h
  change (if (Arlib.Computation.Charged.foldlWhile (fun acc i => body i acc)
    (List.range s.restartCap) (some start, false)).val.2 then
    pure (Arlib.Computation.Charged.foldlWhile (fun acc i => body i acc)
      (List.range s.restartCap) (some start, false)).val.1
    else pure none : Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val =
      some result at h
  split at h
  · rename_i hd
    exact hscan result h hd
  · cases h

/-- INTERNAL: The concrete fresh-bit restart set is classified as a
transversal on every tape, including the empty ground.
TEXLINE: main.tex:1163-1176 -/
theorem freshTransversal_transversal (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    (classifyState (freshTransversal n tape cursor).val.1).val = .transversal := by
  rw [InitialRestartLaw.freshTransversal_value]
  let state : PairedSet n := Finset.univ.image (fun i : Fin n => (i, tape (cursor + i)))
  have hpair (i : Fin n) (b : Bool) : (i, b) ∈ state ↔ tape (cursor + i) = b := by
    simp [state, Finset.mem_image, Prod.mk.injEq]
  let visit := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) => do
    let x ← containsPaired state (i, false)
    let y ← containsPaired state (i, true)
    if x then
      if y then
        let seen ← isSome acc.2.1
        if seen then pure (acc.1, acc.2.1, true)
        else pure (acc.1, some i, acc.2.2)
      else pure acc
    else
      if y then pure acc
      else
        let seen ← isSome acc.1
        if seen then pure (acc.1, acc.2.1, true)
        else pure (some i, acc.2.1, acc.2.2)
  have hvisit (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
      (visit acc i).val = acc := by
    cases ht : tape (cursor + i) <;>
      simp [visit, containsPaired, hpair, ht]
  have hfold (xs : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
      (Arlib.Computation.Charged.foldl visit xs acc).val = acc := by
    induction xs generalizing acc with
    | nil => rfl
    | cons i xs ih => rw [Arlib.Computation.Charged.val_foldl_cons, hvisit, ih]
  change (classifyState state).val = .transversal
  unfold classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl visit (List.finRange n) (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) : Arlib.Computation.Charged Op Cell (StateKind n)).val = _
  rw [Arlib.Computation.Charged.val_bind, hfold]
  rfl

/-- INTERNAL: Every successful actual phase restart returns a transversal;
empty crossed-stage and trace loops retain the fresh transversal.
TEXLINE: main.tex:1163-1176 -/
theorem restartPhase_transversal {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (result : PairedSet n × ℕ)
    (h : (restartPhase r o₁ o₂ tape s tables j cursor).val = some result) :
    (classifyState result.1).val = .transversal := by
  let P : Option (RestartCursor n) → Prop := fun outcome =>
    ∀ current, outcome = some current →
      (classifyState current.state).val = .transversal
  have hfold (f : Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (RestartCursor n)))
      (hf : ∀ current i, P current → P (f current i).val)
      (xs : List ℕ) (current : Option (RestartCursor n)) (hc : P current) :
      P (Arlib.Computation.Charged.foldl f xs current).val := by
    induction xs generalizing current with
    | nil => exact hc
    | cons i xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        exact ih _ (hf current i hc)
  let stage : Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (RestartCursor n)) :=
    fun current index => do
      match current with
      | none => pure none
      | some current =>
          let a ← successor index
          let q ← ratPower s.ρ a
          let weights ← learnedWeightRead tables a s.L
          Arlib.Computation.Charged.repeatFor (fun _ current => do
            match current with
            | none => pure none
            | some current => traceReturn r o₁ o₂ tape s q weights current)
            s.τ (some current)
  have hstage : ∀ current i, P current → P (stage current i).val := by
    intro current i hp
    cases current with
    | none => intro next hn; cases hn
    | some current =>
        dsimp only [stage]
        simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
        apply hfold
        · intro outcome a _ next hn
          cases outcome with
          | none => cases hn
          | some previous => exact traceReturn_transversal r o₁ o₂ tape s _ _ previous next hn
        · exact hp
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape cursor).val.1, (freshTransversal n tape cursor).val.2, 0⟩
  have hinitial : P (some initial) := by
    intro current hc
    have heq := Option.some.inj hc
    subst current
    exact freshTransversal_transversal n tape cursor
  have hcross := hfold stage hstage (List.range j) (some initial) hinitial
  unfold restartPhase at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor] at h
  change (match (Arlib.Computation.Charged.foldl stage (List.range j) (some initial)).val with
    | none => pure none
    | some next => pure (some (next.state, next.bitCursor)) :
      Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val = some result at h
  cases hc : (Arlib.Computation.Charged.foldl stage (List.range j) (some initial)).val with
  | none => simp only [hc, Arlib.Computation.Charged.val_pure] at h; cases h
  | some next =>
      simp only [hc, Arlib.Computation.Charged.val_pure] at h
      have heq := Option.some.inj h
      subst result
      exact hcross next hc

end CountingMatroid.Analysis.RestartPhaseTransversal
