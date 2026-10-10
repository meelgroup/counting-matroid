import CountingMatroid.Analysis.RestartDrawProbe
import CountingMatroid.Analysis.RestartDrawProbeScanReplay

set_option autoImplicit false

/-!
Pre-draw replay for the concrete ordinal probe, independent of schedule
arithmetic, finite-prefix packaging, or probability. The probe's descriptor
depends only on the tape between the restart cursor and the descriptor's own
cursor, even though the counted state continues reading afterwards. The proof
packages a per-step replay contract (`ProbeStep`) — sticky capture, inert
death, silence past the ordinal, capture replay, and quiet whole-value replay
— shows it for one trace transition from the scan lemmas, and closes it under
the transition and stage folds.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeReplay
open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartDrawProbe

/-- INTERNAL: The replay contract of one fresh-observation step of the probe
over accumulators `((state, count), observed)`: a captured descriptor is sticky;
a dead state is inert; a step entered past the ordinal never captures; a
capture replays from the entering floor to the descriptor cursor; and a quiet
live step ending at or before the ordinal replays its whole value from the
floor to its own cursor. The contract is closed under folds.
TEXLINE: main.tex:1163-1176,1392-1421 -/
structure ProbeStep {X : Type} (bc : X → ℕ) (ordinal : ℕ)
    (T : (ℕ → Bool) → (Option X × ℕ) × Option (ℕ × ℕ) → (Option X × ℕ) × Option (ℕ × ℕ)) :
    Prop where
  sticky : ∀ tape acc d, acc.2 = some d → (T tape acc).2 = some d
  dead : ∀ tape count, T tape ((none, count), none) = ((none, count), none)
  past : ∀ tape acc, acc.2 = none → ordinal < acc.1.2 →
    (T tape acc).2 = none ∧ ordinal < (T tape acc).1.2
  capture : ∀ cur count floor, floor ≤ bc cur →
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => (T tape ((some cur, count), none)).2) Prod.fst floor
  quiet : ∀ cur count floor, floor ≤ bc cur → ∀ tape c count',
    T tape ((some cur, count), none) = ((some c, count'), none) → count' ≤ ordinal →
    floor ≤ bc c ∧ ∀ other, (∀ i, floor ≤ i → i < bc c → tape i = other i) →
      T other ((some cur, count), none) = ((some c, count'), none)

/-- INTERNAL: A fold of probe steps satisfying the replay contract satisfies it. -/
theorem probeStep_foldl {X α : Type} (bc : X → ℕ) (ordinal : ℕ)
    (f : (ℕ → Bool) → (Option X × ℕ) × Option (ℕ × ℕ) → α →
      Arlib.Computation.Charged Op Cell ((Option X × ℕ) × Option (ℕ × ℕ)))
    (hf : ∀ a, ProbeStep bc ordinal (fun tape acc => (f tape acc a).val)) (xs : List α) :
    ProbeStep bc ordinal
      (fun tape acc => (Arlib.Computation.Charged.foldl (f tape) xs acc).val) := by
  induction xs with
  | nil =>
    refine ⟨fun _ _ _ h => h, fun _ _ => rfl, fun _ _ h1 h2 => ⟨h1, h2⟩, ?_, ?_⟩
    · intro cur count floor _ tape out h
      cases h
    · intro cur count floor hfl tape c count' h _
      simp only [Arlib.Computation.Charged.val_foldl_nil, Prod.mk.injEq, Option.some.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, -⟩ := h
      exact ⟨hfl, fun _ _ => rfl⟩
  | cons a xs ih =>
    have ha := hf a
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro tape acc d h
      simp only [Arlib.Computation.Charged.val_foldl_cons]
      exact ih.sticky tape _ d (ha.sticky tape acc d h)
    · intro tape count
      simp only [Arlib.Computation.Charged.val_foldl_cons]
      rw [ha.dead tape count]
      exact ih.dead tape count
    · intro tape acc h1 h2
      simp only [Arlib.Computation.Charged.val_foldl_cons]
      have hm := ha.past tape acc h1 h2
      exact ih.past tape _ hm.1 hm.2
    · intro cur count floor hfl tape out h
      simp only [Arlib.Computation.Charged.val_foldl_cons] at h
      cases hmid : (f tape ((some cur, count), none) a).val with
      | mk mid1 obs =>
      obtain ⟨st, cnt⟩ := mid1
      cases obs with
      | some d =>
        have hd := ih.sticky tape ((st, cnt), some d) d rfl
        rw [hmid, hd] at h
        have hdo : d = out := Option.some.inj h
        subst hdo
        have hc := ha.capture cur count floor hfl tape d (by simp only [hmid])
        refine ⟨hc.1, fun other hagree => ?_⟩
        have ho := hc.2 other hagree
        simp only [Arlib.Computation.Charged.val_foldl_cons]
        exact ih.sticky other _ d ho
      | none =>
        cases st with
        | none =>
          rw [hmid, ih.dead] at h
          cases h
        | some c =>
          by_cases hcnt : ordinal < cnt
          · rw [hmid, (ih.past tape _ rfl hcnt).1] at h
            cases h
          · have hq := ha.quiet cur count floor hfl tape c cnt hmid (by omega)
            rw [hmid] at h
            have hr := ih.capture c cnt (bc c) (le_refl _) tape out h
            refine ⟨hq.1.trans hr.1, fun other hagree => ?_⟩
            have h1 := hq.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hr.1))
            have h2 := hr.2 other (fun i hlo hhi => hagree i (hq.1.trans hlo) hhi)
            simp only [Arlib.Computation.Charged.val_foldl_cons]
            rw [h1]
            exact h2
    · intro cur count floor hfl tape c count' h hle
      simp only [Arlib.Computation.Charged.val_foldl_cons] at h
      cases hmid : (f tape ((some cur, count), none) a).val with
      | mk mid1 obs =>
      obtain ⟨st, cnt⟩ := mid1
      cases obs with
      | some d =>
        have hd := ih.sticky tape ((st, cnt), some d) d rfl
        rw [hmid] at h
        rw [h] at hd
        cases hd
      | none =>
        cases st with
        | none =>
          rw [hmid, ih.dead] at h
          cases h
        | some c1 =>
          by_cases hcnt : ordinal < cnt
          · have hp := (ih.past tape ((some c1, cnt), none) rfl hcnt).2
            rw [← hmid, h] at hp
            exact absurd hle (by simpa using hp)
          · have hq := ha.quiet cur count floor hfl tape c1 cnt hmid (by omega)
            rw [hmid] at h
            have hr := ih.quiet c1 cnt (bc c1) (le_refl _) tape c count' h hle
            refine ⟨hq.1.trans hr.1, fun other hagree => ?_⟩
            have h1 := hq.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hr.1))
            have h2 := hr.2 other (fun i hlo hhi => hagree i (hq.1.trans hlo) hhi)
            simp only [Arlib.Computation.Charged.val_foldl_cons]
            rw [h1]
            exact h2

/-- INTERNAL: Unfold the probe's return to its capped scan. -/
theorem probedReturn_val {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n) (count : ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val =
      (fun scan : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ) =>
        (((if scan.1.1.2 then scan.1.1.1 else none), scan.1.2), scan.2))
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
          (List.range s.restartCap) (((some start, false), count), observed)).val := rfl

/-- INTERNAL: One trace transition of the probe meets the replay contract,
by the scan-level replay lemmas. -/
theorem probedTransition_step {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3) :
    ProbeStep RestartCursor.bitCursor ordinal
      (fun tape acc => (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro tape acc d h
    obtain ⟨⟨st, count⟩, obs⟩ := acc
    cases st with
    | none => exact h
    | some cur =>
      simp only at h
      subst h
      exact probed_return_retains r o₁ o₂ tape s q w ordinal draw cur count d
  · intro tape count
    rfl
  · intro tape acc h1 h2
    obtain ⟨⟨st, count⟩, obs⟩ := acc
    simp only at h1 h2
    subst h1
    cases st with
    | none => exact ⟨rfl, h2⟩
    | some cur =>
      change (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val.2 = none ∧
        ordinal < (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val.1.2
      rw [probedReturn_val]
      refine ⟨RestartDrawProbeScanReplay.probedBody_scan_past r o₁ o₂ tape s q w ordinal draw
        _ _ count h2, ?_⟩
      exact h2.trans_le (RestartDrawProbeScanReplay.probedBody_scan_count_mono r o₁ o₂ tape s
        q w ordinal draw _ (((some cur, false), count), none))
  · intro cur count floor hfl tape out h
    have hr := RestartDrawProbeScanReplay.probedBody_scan_replay r o₁ o₂ s q w ordinal draw
      (List.range s.restartCap) (some cur, false) count floor
      (fun c hc => by cases hc; exact hfl) tape out (by
        change (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val.2 = some out
          at h
        rw [probedReturn_val] at h
        exact h)
    refine ⟨hr.1, fun other hagree => ?_⟩
    change (probedReturn r o₁ o₂ other s q w ordinal draw cur count none).val.2 = some out
    rw [probedReturn_val]
    exact hr.2 other hagree
  · intro cur count floor hfl tape c count' h hle
    change (probedReturn r o₁ o₂ tape s q w ordinal draw cur count none).val =
      ((some c, count'), none) at h
    rw [probedReturn_val] at h
    cases hscan : (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc)
        (List.range s.restartCap) (((some cur, false), count), none)).val with
    | mk scan1 obs =>
    obtain ⟨⟨st, done⟩, cnt⟩ := scan1
    rw [hscan] at h
    cases done with
    | false => simp at h
    | true =>
      simp only [if_true, Prod.mk.injEq] at h
      obtain ⟨⟨rfl, rfl⟩, rfl⟩ := h
      have hq := RestartDrawProbeScanReplay.probedBody_scan_quiet_replay r o₁ o₂ s q w ordinal
        draw (List.range s.restartCap) cur false count floor hfl tape c
        (by rw [hscan]) (by rw [hscan]) (by rw [hscan]; exact hle)
      refine ⟨hq.1, fun other hagree => ?_⟩
      show (probedReturn r o₁ o₂ other s q w ordinal draw cur count none).val = _
      rw [probedReturn_val, hq.2 other hagree, hscan]
      rfl

/-- INTERNAL: One stage of the probe meets the replay contract; its parameter
and stored multipliers do not read the tape. -/
theorem probedStage_step {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (ordinal : ℕ) (draw : Fin 3)
    (index : ℕ) :
    ProbeStep RestartCursor.bitCursor ordinal
      (fun tape acc => (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val) := by
  have h := probeStep_foldl RestartCursor.bitCursor ordinal
    (fun tape acc (_ : ℕ) => probedTransition r o₁ o₂ tape s
      (ratPower s.ρ (successor index).val).val
      (learnedWeightRead tables (successor index).val s.L).val ordinal draw acc)
    (fun _ => probedTransition_step r o₁ o₂ s _ _ ordinal draw) (List.range s.τ)
  simpa only [probedStage, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.repeatFor] using h

/-- INTERNAL: An ordinal probe depends only on the tape before its reported
absolute cursor, even though the observed restart continues afterwards.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem restart_draw_probe_replay {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tables : LearnedWeights n) (j cursor : ℕ)
    (k : Fin (3 * s.restartCap)) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => restartDrawProbe r o₁ o₂ tape s tables j cursor k)
      Prod.fst cursor := by
  have hfold := probeStep_foldl RestartCursor.bitCursor (k.val / 3)
    (fun tape acc index => probedStage r o₁ o₂ tape s tables (k.val / 3)
      ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ index acc)
    (fun index => probedStage_step r o₁ o₂ s tables (k.val / 3)
      ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ index) (List.range j)
  have hval : ∀ tape, restartDrawProbe r o₁ o₂ tape s tables j cursor k =
      (Arlib.Computation.Charged.foldl
        (fun acc index => probedStage r o₁ o₂ tape s tables (k.val / 3)
          ⟨k.val % 3, Nat.mod_lt _ (by decide)⟩ index acc) (List.range j)
        ((some ⟨Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))),
          cursor + n, 0⟩, 0), none)).val.2 := by
    intro tape
    simp only [restartDrawProbe, probedRestart, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor,
      InitialRestartLaw.freshTransversal_value]
  intro tape d hd
  beta_reduce at hd ⊢
  rw [hval] at hd
  have hc := hfold.capture _ 0 (cursor + n) le_rfl tape d hd
  refine ⟨(Nat.le_add_right cursor n).trans hc.1, fun other hagree => ?_⟩
  rw [hval]
  have himage : Finset.univ.image (fun i : Fin n => (i, other (cursor + i))) =
      Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))) := by
    congr 1
    funext i
    rw [hagree (cursor + i) (Nat.le_add_right _ _) (by have := i.isLt; have := hc.1; omega)]
  rw [himage]
  exact hc.2 other (fun i hlo hhi => hagree i ((Nat.le_add_right cursor n).trans hlo) hhi)

end CountingMatroid.Analysis.RestartDrawProbeReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · replay contract `ProbeStep` closed under folds; lifted
  the scan-level replay of `RestartDrawProbeScanReplay` to the whole restart.
* 2026-10-09 · open · exposed fixed-probe stage fold; generic absorbing-Option
  replay cannot replay the continuing product to the earlier observed cursor.
-/
