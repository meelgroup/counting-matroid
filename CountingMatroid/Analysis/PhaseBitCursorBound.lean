import CountingMatroid.Analysis.ChainStepBitBound
import CountingMatroid.Analysis.PhaseHistoryMultiplierLength
import CountingMatroid.Analysis.InitialRestartLaw

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace CountingMatroid.Analysis.PhaseBitCursorBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: Preserve an invariant across a charged loop with early breaks. -/
private theorem foldWhile_preserves {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β))
    (hf : ∀ b a next, P b → (f b a).val = some next → P next)
    (xs : List α) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldlWhile f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      cases he : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at he ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, he] using hb
      | some next =>
          have hn := ih next (hf b a next hb he)
          simp only [Arlib.Computation.Charged.val] at he hn ⊢
          simpa only [Arlib.Computation.Charged.foldlWhile, he] using hn

/-- INTERNAL: The global restart-attempt counter pays for every underlying
chain step, across positive-time trace returns; the guard enforces the cap.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem traceReturn_preserves_bit_budget {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (base K : ℕ) (start out : RestartCursor n)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (ha : start.attempts ≤ s.restartCap)
    (hb : start.bitCursor ≤ base + start.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1)))
    (h : (traceReturn r o₁ o₂ tape s q weights start).val = some out) :
    out.attempts ≤ s.restartCap ∧
    out.bitCursor ≤ base + out.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  let P : Option (RestartCursor n) → Prop := fun acc =>
    ∀ cur, acc = some cur → cur.attempts ≤ s.restartCap ∧
      cur.bitCursor ≤ base + cur.attempts * C
  let step : (Option (RestartCursor n) × Bool) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (Option (RestartCursor n) × Bool)) :=
    fun acc _ => do
      if acc.2 then pure none
      else match acc.1 with
      | none => pure none
      | some current =>
          let allowed ← lessThan current.attempts s.restartCap
          if allowed then
            let attempted ← chainStep r o₁ o₂ tape s.drawTrials q weights current.state current.bitCursor
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
  have hs : ∀ acc index next, P acc.1 → (step acc index).val = some next → P next.1 := by
    intro acc index next hp he cur hc
    dsimp only [step] at he
    split at he
    · cases he
    · cases ha' : acc.1 with
      | none => simp only [ha', Arlib.Computation.Charged.val_pure] at he; cases he
      | some current =>
          simp only [ha', Arlib.Computation.Charged.val_bind, lessThan,
            Arlib.Computation.Charged.val_op] at he
          split at he
          · rename_i hallowed
            have hlt : current.attempts < s.restartCap := of_decide_eq_true hallowed
            simp only [Arlib.Computation.Charged.val_bind] at he
            cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q weights
                current.state current.bitCursor).val with
            | none =>
                simp only [hchain, Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
                subst next
                cases hc
            | some attempted =>
                simp only [hchain, Arlib.Computation.Charged.val_bind, successor,
                  Arlib.Computation.Charged.val_op] at he
                have hbit := chain_step_bit_bound r o₁ o₂ tape s.drawTrials q weights
                  current.state current.bitCursor K hq hw attempted hchain
                have hcur := (hp current ha').2
                cases attempted with
                | mk state stop =>
                    cases hk : (classifyState state).val <;>
                      simp only [hk, Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure, Option.some.injEq] at he <;>
                      subst next <;> cases Option.some.inj hc <;>
                      exact ⟨by dsimp only; omega, by
                        dsimp only [C, RestartCursor.bitCursor, RestartCursor.attempts] at hcur ⊢
                        rw [Nat.add_mul, Nat.one_mul]
                        omega⟩
          · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
            subst next
            cases hc
  have hscan := foldWhile_preserves (fun acc => P acc.1) step hs
    (List.range s.restartCap) (some start, false)
    (by intro cur he; cases Option.some.inj he; exact ⟨ha, hb⟩)
  unfold traceReturn at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatWhile] at h
  change (if (Arlib.Computation.Charged.foldlWhile step (List.range s.restartCap)
      (some start, false)).val.2 then
    pure (Arlib.Computation.Charged.foldlWhile step (List.range s.restartCap)
      (some start, false)).val.1 else pure none :
    Arlib.Computation.Charged Op Cell (Option (RestartCursor n))).val = some out at h
  split at h
  · exact hscan out h
  · cases h

/-- INTERNAL: A list-indexed charged fold uses only indices in that list. -/
private theorem fold_preserves_mem {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell β) (xs : List α)
    (hf : ∀ b a, a ∈ xs → P b → P (f b a).val) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih (fun b i hi => hf b i (List.mem_cons_of_mem a hi))
        _ (hf b a (List.mem_cons_self) hb)

/-- INTERNAL: Crossing all stored restart kernels shares one attempt budget;
the nested trace-loop counts do not multiply the bit-consumption bound.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_phase_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor K : ℕ) (hj : j ≤ s.L)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K)
    (hw : ∀ phase i, binaryRatLength (tables phase i) ≤ K)
    (out : PairedSet n × ℕ)
    (h : (restartPhase r o₁ o₂ tape s tables j cursor).val = some out) :
    out.2 ≤ cursor + n + s.restartCap * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  let P : Option (RestartCursor n) → Prop := fun acc =>
    ∀ current, acc = some current → current.attempts ≤ s.restartCap ∧
      current.bitCursor ≤ cursor + n + current.attempts * C
  let stage : Option (RestartCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (RestartCursor n)) := fun acc index => do
    match acc with
    | none => pure none
    | some current =>
        let a ← successor index
        let q ← ratPower s.ρ a
        let weights ← learnedWeightRead tables a s.L
        Arlib.Computation.Charged.repeatFor (fun _ acc => do
          match acc with
          | none => pure none
          | some current => traceReturn r o₁ o₂ tape s q weights current)
          s.τ (some current)
  have hs : ∀ acc index, index ∈ List.range j → P acc → P (stage acc index).val := by
    intro acc index hi hp
    have hi' : index + 1 ≤ s.L := by have := List.mem_range.mp hi; omega
    cases acc with
    | none => intro out he; cases he
    | some current =>
        dsimp only [stage]
        simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor]
        apply chargedFold_preserves P
        · intro acc i hb next he
          cases acc with
          | none => cases he
          | some current =>
              have hc := hb current rfl
              apply traceReturn_preserves_bit_budget r o₁ o₂ tape s _ _ (cursor + n) K
                current next ?_ ?_ hc.1 hc.2 he
              · have hl := ratPower_binary_length_le s.ρ (index + 1)
                have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) hi'
                have hh := Nat.mul_le_mul_left n (hl.trans (Nat.add_le_add_left hm _))
                change binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ (index + 1)).val ≤ K
                exact (Nat.add_le_add_left hh _).trans hq
              · simpa only [learnedWeightRead, successor, Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_opMany]
                  using hw (index + 1)
        · exact hp
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape cursor).val.1, (freshTransversal n tape cursor).val.2, 0⟩
  have hi : P (some initial) := by
    intro cur he
    cases Option.some.inj he
    simp only [initial, InitialRestartLaw.freshTransversal_value, Nat.zero_mul, Nat.add_zero]
    exact ⟨Nat.zero_le _, le_rfl⟩
  have hf := fold_preserves_mem P stage (List.range j) hs (some initial) hi
  unfold restartPhase at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.repeatFor] at h
  change (match (Arlib.Computation.Charged.foldl stage (List.range j) (some initial)).val with
    | none => pure none
    | some result => pure (some (result.state, result.bitCursor)) :
    Arlib.Computation.Charged Op Cell (Option (PairedSet n × ℕ))).val = some out at h
  split at h
  · cases h
  · rename_i result he
    have heq := Option.some.inj h
    rw [← heq]
    have hb := hf result he
    exact hb.2.trans (Nat.add_le_add_left (Nat.mul_le_mul_right C hb.1) _)

/-- INTERNAL: Recording an observation consumes no fair bits. -/
private theorem record_cursor {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    next.bitCursor = current.bitCursor := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · cases h
  · exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm
  · simp only [Arlib.Computation.Charged.val_bind] at h
    exact (congrArg ObservationCursor.bitCursor (Option.some.inj h)).symm

/-- INTERNAL: Each iteration of the actual observation prefix consumes at
most one bounded chain attempt; the initial record consumes none.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem observe_phase_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (out : ObservationCursor n)
    (h : (observePhase r o₁ o₂ tape s q weights start).val = some out) :
    out.bitCursor ≤ start.2 + s.observations * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  let P : Option (ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ cur, acc = some cur → cur.bitCursor ≤ start.2 + k * C
  let step : Option (ObservationCursor n) → ℕ →
      Arlib.Computation.Charged Op Cell (Option (ObservationCursor n)) := fun acc index => do
    match acc with
    | none => pure none
    | some current =>
        let onStart ← natEqual index 0
        if onStart then recordObservation r o₁ o₂ s.ρ current
        else
          let next ← chainStep r o₁ o₂ tape s.drawTrials q weights current.state current.bitCursor
          match next with
          | none => pure none
          | some (state, bitCursor) =>
              recordObservation r o₁ o₂ s.ρ ⟨state, bitCursor, current.counts, current.numeratorSum⟩
  have hs : ∀ acc index k, P acc k → P (step acc index).val (k + 1) := by
    intro acc index k hp next hn
    cases acc with
    | none => cases hn
    | some current =>
        dsimp only [step] at hn
        simp only [Arlib.Computation.Charged.val_bind] at hn
        have hc := hp current rfl
        split at hn
        · have he := record_cursor r o₁ o₂ s.ρ current next hn
          dsimp only [C] at hc ⊢
          rw [he, Nat.add_mul, Nat.one_mul]
          omega
        · simp only [Arlib.Computation.Charged.val_bind] at hn
          cases he : (chainStep r o₁ o₂ tape s.drawTrials q weights current.state current.bitCursor).val with
          | none => simp only [he, Arlib.Computation.Charged.val_pure] at hn; cases hn
          | some attempted =>
              cases attempted with
              | mk state stop =>
                  simp only [he] at hn
                  have heq := record_cursor r o₁ o₂ s.ρ _ next hn
                  have hb := chain_step_bit_bound r o₁ o₂ tape s.drawTrials q weights
                    current.state current.bitCursor K hq hw (state, stop) he
                  dsimp only [C] at hc ⊢
                  rw [heq, Nat.add_mul, Nat.one_mul]
                  dsimp only at hb ⊢
                  omega
  let initial : ObservationCursor n := ⟨start.1, start.2, (allocateCounts n).val, 0⟩
  have hf := chargedFold_count_growth P step hs (List.range s.observations)
    (some initial) 0 (by intro cur he; cases Option.some.inj he; simp [initial])
  change (Arlib.Computation.Charged.foldl step (List.range s.observations) (some initial)).val = some out at h
  simpa only [List.length_range, Nat.zero_add] using hf out h

/-- INTERNAL: Sum restart and observation budgets across the actual history,
using the additive bound on its current and learned multipliers.
TEXLINE: main.tex:1356-1390,1392-1421 -/
theorem phase_history_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (j K : ℕ) (hj : j ≤ s.L)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K)
    (hw : 6 + s.L * (n * n * (4 * (s.observations + 4))) ≤ K)
    (current : AnnealingCursor n)
    (h : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j = some current) :
    current.bitCursor ≤ j *
      (n + (s.restartCap + s.observations) * (1 + 3 * s.drawTrials * (4 * K + n + 1))) := by
  induction j generalizing current with
  | zero =>
      have he : BoundedRunPhaseHistory.initialCursor n s = current := Option.some.inj h
      subst current
      simp [BoundedRunPhaseHistory.initialCursor]
  | succ j ih =>
      rw [BoundedRunPhaseHistory.phaseHistory_succ] at h
      cases hp : BoundedRunPhaseHistory.phaseHistory r o₁ o₂ tape s j with
      | none => simp [hp, BoundedRunPhase.boundedRunPhase] at h
      | some previous =>
          rw [hp] at h
          have hprevious := ih (by omega) previous hp
          have hsize := PhaseHistoryMultiplierLength.phase_history_multiplier_length_le
            r o₁ o₂ tape s j previous hp
          have htable : ∀ phase i, binaryRatLength (previous.tables phase i) ≤ K := by
            intro phase i
            apply (hsize.2 phase i).trans
            exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : j ≤ s.L)) _).trans hw
          have hweights : ∀ i, binaryRatLength (previous.currentWeights i) ≤ K := by
            intro i
            apply (hsize.1 i).trans
            exact (Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega : j ≤ s.L)) _).trans hw
          unfold BoundedRunPhase.boundedRunPhase at h
          simp only [Arlib.Computation.Charged.val_bind] at h
          cases hs : (restartPhase r o₁ o₂ tape s previous.tables j previous.bitCursor).val with
          | none => simp [hs] at h
          | some started =>
              simp only [hs, Arlib.Computation.Charged.val_bind] at h
              cases ho : (observePhase r o₁ o₂ tape s (ratPower s.ρ j).val
                  previous.currentWeights started).val with
              | none => simp [ho] at h
              | some observed =>
                  simp only [ho, Arlib.Computation.Charged.val_bind] at h
                  cases hf : (finishPhase s j previous.currentWeights observed).val with
                  | none => simp [hf] at h
                  | some finished =>
                      simp only [hf, Arlib.Computation.Charged.val_bind] at h
                      have hcursor : current.bitCursor = observed.bitCursor := by
                        by_cases hu : (lessThan (successor j).val s.L).val = true
                        · rw [if_pos hu] at h
                          simp only [Arlib.Computation.Charged.val_bind] at h
                          exact (congrArg AnnealingCursor.bitCursor (Option.some.inj h)).symm
                        · rw [if_neg hu] at h
                          exact (congrArg AnnealingCursor.bitCursor (Option.some.inj h)).symm
                      have hqj : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ j).val ≤ K := by
                        have hl := ratPower_binary_length_le s.ρ j
                        have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) (show j ≤ s.L by omega)
                        exact (Nat.add_le_add_left (Nat.mul_le_mul_left n
                          (hl.trans (Nat.add_le_add_left hm _))) _).trans hq
                      have hrs := restart_phase_bit_bound r o₁ o₂ tape s previous.tables
                        j previous.bitCursor K (by omega) hq htable started hs
                      have hob := observe_phase_bit_bound r o₁ o₂ tape s (ratPower s.ρ j).val
                        previous.currentWeights started K hqj hweights observed ho
                      let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
                      change previous.bitCursor ≤ j * (n + (s.restartCap + s.observations) * C) at hprevious
                      change started.2 ≤ previous.bitCursor + n + s.restartCap * C at hrs
                      change observed.bitCursor ≤ started.2 + s.observations * C at hob
                      change current.bitCursor ≤ (j + 1) * (n + (s.restartCap + s.observations) * C)
                      rw [hcursor]
                      calc
                        observed.bitCursor ≤ started.2 + s.observations * C := hob
                        _ ≤ previous.bitCursor + n + s.restartCap * C + s.observations * C :=
                          Nat.add_le_add_right hrs _
                        _ ≤ j * (n + (s.restartCap + s.observations) * C) + n +
                            s.restartCap * C + s.observations * C := by omega
                        _ = (j + 1) * (n + (s.restartCap + s.observations) * C) := by ring

end CountingMatroid.Analysis.PhaseBitCursorBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved · completed actual-history cursor induction after rejected handoff; both deterministic finishing branches copy the observation cursor. Standalone source elaboration passed.

* this round · proved the global attempt-token invariant for trace returns, restart budget, and observation budget; attempted actual-history induction through zero, abort, and successful predecessor branches. The successful phase cursor composition remains open for the live OPEN handoff.
-/
