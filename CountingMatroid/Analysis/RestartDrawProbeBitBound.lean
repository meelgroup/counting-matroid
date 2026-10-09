import CountingMatroid.Analysis.RestartDrawProbe
import CountingMatroid.Analysis.ChainStepBitBound
import CountingMatroid.Analysis.PhaseResourcePrimitives

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Quantitative bit-cursor coverage for a single probed restart ordinal,
retained even when the probed attempt later aborts. The argument mirrors
the chain/restart bit-budget invariant used for a completed restart, but
tracks the first captured draw descriptor instead of the loop's final
output.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.ChainStepBitBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: Joint per-attempt invariant: the retained restart cursor fits
the per-attempt budget and matches the separate attempt counter, and any
already-captured descriptor already satisfies the final site bound. -/
private def ProbeInv {n : ℕ} (s : AnnealingSchedule) (base _K C : ℕ)
    (cur : Option (RestartCursor n)) (count : ℕ) (observed : Option (ℕ × ℕ)) : Prop :=
  (∀ current, cur = some current →
    current.attempts ≤ s.restartCap ∧
    current.bitCursor ≤ base + current.attempts * C ∧
    count = current.attempts) ∧
  (∀ d, observed = some d →
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤ base + s.restartCap * C)

/-- INTERNAL: Preserve an invariant across a charged early-break loop. -/
private theorem foldWhile_inv {α β : Type} (P : β → Prop)
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

/-- INTERNAL: A list-indexed charged fold preserves an invariant using only
the list membership of the index actually consumed. -/
private theorem fold_mem_inv {α β : Type} (P : β → Prop)
    (f : β → α → Arlib.Computation.Charged Op Cell β) (xs : List α)
    (hf : ∀ b a, a ∈ xs → P b → P (f b a).val) (b : β) (hb : P b) :
    P (Arlib.Computation.Charged.foldl f xs b).val := by
  induction xs generalizing b with
  | nil => exact hb
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      exact ih (fun b i hi => hf b i (List.mem_cons_of_mem a hi))
        _ (hf b a List.mem_cons_self hb)

/-- INTERNAL: One probed body call extends the joint invariant, using the
original chain-step and chain-draw-site bit bounds. -/
private theorem probedBody_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (w i) ≤ K) (ordinal : ℕ) (draw : Fin 3)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
    (hacc : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      acc.1.1.1 acc.1.2 acc.2)
    (next : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ))
    (he : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val = some next) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      next.1.1.1 next.1.2 next.2 := by
  obtain ⟨⟨⟨cur0, stop0⟩, count0⟩, obs0⟩ := acc
  obtain ⟨hcur0, hobs0⟩ := hacc
  simp only [probedBody, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Option.map_eq_some_iff] at he
  obtain ⟨result, hresult, hnext⟩ := he
  have hnext1 : next.1 = result := congrArg Prod.fst hnext.symm
  have hnext2 : next.2 =
      obs0.or (bodySite r o₁ o₂ tape s q w ordinal draw ((cur0, stop0), count0)) :=
    congrArg Prod.snd hnext.symm
  refine ⟨?_, ?_⟩
  · intro current hcurrent
    rw [hnext1] at hcurrent
    unfold countedBody at hresult
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
      Option.map_eq_some_iff] at hresult
    obtain ⟨tbresult, htb, hre⟩ := hresult
    have hre1 : result.1 = tbresult := congrArg Prod.fst hre.symm
    have hre2 : result.2 = count0 + attemptIncrement s (cur0, stop0) := congrArg Prod.snd hre.symm
    rw [hre1] at hcurrent
    unfold traceBody at htb
    split at htb
    · simp only [Arlib.Computation.Charged.val_pure] at htb
      cases htb
    · rename_i hstop
      cases hcc : cur0 with
      | none => simp only [hcc, Arlib.Computation.Charged.val_pure] at htb; cases htb
      | some current0 =>
          simp only [hcc, Arlib.Computation.Charged.val_bind, lessThan,
            Arlib.Computation.Charged.val_op] at htb
          split at htb
          · rename_i hallowed
            have hlt : current0.attempts < s.restartCap := of_decide_eq_true hallowed
            simp only [Arlib.Computation.Charged.val_bind] at htb
            cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q w
                current0.state current0.bitCursor).val with
            | none =>
                simp only [hchain, Arlib.Computation.Charged.val_pure,
                  Option.some.injEq] at htb
                rw [← htb] at hcurrent
                cases hcurrent
            | some attempted =>
                simp only [hchain, Arlib.Computation.Charged.val_bind, successor,
                  Arlib.Computation.Charged.val_op] at htb
                have hbit := chain_step_bit_bound r o₁ o₂ tape s.drawTrials q w
                  current0.state current0.bitCursor K hq hw attempted hchain
                obtain ⟨hattempt0, hbit0, hcount0⟩ := hcur0 current0 hcc
                have hcount0' : count0 = current0.attempts := hcount0
                have hinc : attemptIncrement s (cur0, stop0) = 1 := by
                  unfold attemptIncrement
                  rw [if_neg hstop, hcc]
                  exact if_pos hlt
                have hnext12 : next.1.2 = result.2 := congrArg Prod.snd hnext1
                cases attempted with
                | mk state stop =>
                    cases hk : (classifyState state).val <;>
                      simp only [hk, Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_pure, Option.some.injEq] at htb <;>
                      rw [← htb] at hcurrent <;> cases hcurrent <;> dsimp only <;>
                      refine ⟨by omega, by
                        have hC : current0.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1))
                            + (1 + 3 * s.drawTrials * (4 * K + n + 1)) =
                            (current0.attempts + 1) *
                              (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by ring
                        omega, by omega⟩
          · simp only [Arlib.Computation.Charged.val_pure, Option.some.injEq] at htb
            rw [← htb] at hcurrent
            cases hcurrent
  · intro d hd
    rw [hnext2] at hd
    cases ho : obs0 with
    | some old =>
        simp only [ho, Option.some_or, Option.some.injEq] at hd
        exact hobs0 d (by rw [ho, hd])
    | none =>
        simp only [ho, Option.none_or] at hd
        unfold bodySite at hd
        split at hd
        · cases hd
        · cases hcc : cur0 with
          | none => simp only [hcc] at hd; cases hd
          | some current0 =>
              simp only [hcc] at hd
              split at hd
              · rename_i hcond
                obtain ⟨hlt, hcount⟩ := hcond
                obtain ⟨hattempt0, hbit0, hcount0⟩ := hcur0 current0 hcc
                have hchain := chain_draw_site_bit_bound r o₁ o₂ tape s q w
                  current0.state current0.bitCursor K hq hw draw d hd
                have hCeq : current0.attempts * (1 + 3 * s.drawTrials * (4 * K + n + 1))
                    + (1 + 3 * s.drawTrials * (4 * K + n + 1)) =
                    (current0.attempts + 1) * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
                  ring
                have hCle : (current0.attempts + 1) *
                    (1 + 3 * s.drawTrials * (4 * K + n + 1)) ≤
                    s.restartCap * (1 + 3 * s.drawTrials * (4 * K + n + 1)) :=
                  Nat.mul_le_mul_right _ (by omega)
                omega
              · cases hd

/-- INTERNAL: The joint invariant survives a full capped return scan. -/
private theorem probedReturn_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (w i) ≤ K) (ordinal : ℕ) (draw : Fin 3)
    (start : RestartCursor n) (count : ℕ) (observed : Option (ℕ × ℕ))
    (hstart : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (some start) count observed) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.1.1
      (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.1.2
      (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val.2 := by
  have hscan := foldWhile_inv
    (fun acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ) =>
      ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1)) acc.1.1.1 acc.1.2 acc.2)
    (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
    (fun acc _ next ha he => probedBody_inv r o₁ o₂ tape s q w base K hq hw ordinal draw
      acc ha next he)
    (List.range s.restartCap) (((some start, false), count), observed) hstart
  unfold probedReturn
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.repeatWhile]
  split
  · exact hscan
  · exact ⟨fun current hcurrent => by simp at hcurrent, hscan.2⟩

/-- INTERNAL: The joint invariant survives one trace transition. -/
private theorem probedTransition_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (base K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (w i) ≤ K) (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
    (hacc : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      acc.1.1 acc.1.2 acc.2) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.1.1
      (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.1.2
      (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val.2 := by
  unfold probedTransition
  cases hc : acc.1.1 with
  | none =>
      simp only [Arlib.Computation.Charged.val_pure]
      exact hacc
  | some current =>
      rw [hc] at hacc
      exact probedReturn_inv r o₁ o₂ tape s q w base K hq hw ordinal draw current acc.1.2 acc.2
        hacc

/-- INTERNAL: The joint invariant survives a fixed-weight stage of trace
transitions. -/
private theorem probedStage_inv {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (base K : ℕ) (ordinal : ℕ) (draw : Fin 3) (index : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ (index + 1)).val ≤ K)
    (hw : ∀ i, binaryRatLength ((learnedWeightRead tables (index + 1) s.L).val i) ≤ K)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ))
    (hacc : ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      acc.1.1 acc.1.2 acc.2) :
    ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1))
      (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.1
      (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.2
      (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.2 := by
  unfold probedStage
  simp only [Arlib.Computation.Charged.val_bind, successor, ratPower, learnedWeightRead,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]
  exact chargedFold_preserves
    (fun acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ) =>
      ProbeInv s base K (1 + 3 * s.drawTrials * (4 * K + n + 1)) acc.1.1 acc.1.2 acc.2)
    (fun acc (_ : ℕ) => probedTransition r o₁ o₂ tape s
      (ratPower s.ρ (index + 1)).val (learnedWeightRead tables (index + 1) s.L).val ordinal draw acc)
    (fun acc _ ha => probedTransition_inv r o₁ o₂ tape s _ _ base K hq hw ordinal draw acc ha)
    (List.range s.τ) acc hacc

/-- INTERNAL: The complete probed restart has a captured descriptor fitting
the whole restart's shared attempt budget.
TEXLINE: main.tex:1350-1390,1392-1421 -/
theorem restart_draw_probe_bit_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor K : ℕ) (hj : j ≤ s.L)
    (hq : binaryRatLength 1 + n * (binaryRatLength 1 + s.L * binaryRatLength s.ρ) ≤ K)
    (hw : ∀ phase i, binaryRatLength (tables phase i) ≤ K)
    (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ)
    (h : (probedRestart r o₁ o₂ tape s tables j cursor ordinal draw).val.2 = some d) :
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
      cursor + n + s.restartCap * (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let C := 1 + 3 * s.drawTrials * (4 * K + n + 1)
  have hs : ∀ (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) (index : ℕ),
      index ∈ List.range j → ProbeInv s (cursor + n) K C acc.1.1 acc.1.2 acc.2 →
      ProbeInv s (cursor + n) K C
        (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.1
        (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.1.2
        (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val.2 := by
    intro acc index hi hacc
    have hi' : index + 1 ≤ s.L := by
      have := List.mem_range.mp hi
      omega
    have hqj : binaryRatLength 1 + n * binaryRatLength (ratPower s.ρ (index + 1)).val ≤ K := by
      have hl := BoundedRunResourceEnvelope.ratPower_binary_length_le s.ρ (index + 1)
      have hm := Nat.mul_le_mul_right (binaryRatLength s.ρ) hi'
      have hh := Nat.mul_le_mul_left n (hl.trans (Nat.add_le_add_left hm _))
      exact (Nat.add_le_add_left hh _).trans hq
    have hwj : ∀ i, binaryRatLength ((learnedWeightRead tables (index + 1) s.L).val i) ≤ K := by
      simpa only [learnedWeightRead, successor, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany] using hw (index + 1)
    exact probedStage_inv r o₁ o₂ tape s tables (cursor + n) K ordinal draw index hqj hwj acc hacc
  let initial : RestartCursor n :=
    ⟨(freshTransversal n tape cursor).val.1, (freshTransversal n tape cursor).val.2, 0⟩
  have hi : ProbeInv s (cursor + n) K C (some initial) 0 none := by
    refine ⟨?_, ?_⟩
    · intro current hcurrent
      cases hcurrent
      simp only [initial, InitialRestartLaw.freshTransversal_value, Nat.zero_mul, Nat.add_zero]
      exact ⟨Nat.zero_le _, le_rfl, trivial⟩
    · intro d' hd'
      cases hd'
  have hf := fold_mem_inv
    (fun acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ) =>
      ProbeInv s (cursor + n) K C acc.1.1 acc.1.2 acc.2)
    (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
    (List.range j) hs ((some initial, 0), none) hi
  unfold probedRestart at h
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.repeatFor] at h
  have h2 : (Arlib.Computation.Charged.foldl
      (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc)
      (List.range j) ((some initial, 0), none)).val.2 = some d := h
  exact hf.2 d h2

end CountingMatroid.Analysis.RestartDrawProbeBitBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · new · joint attempt/cursor/descriptor invariant propagated
  through the probed-restart fold, giving a shared-budget bound on any
  captured ordinal draw descriptor even on a later abort.
-/
