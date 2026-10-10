import CountingMatroid.Analysis.ChainDrawAbortAttribution
import CountingMatroid.Analysis.ChainStepNoninvalid
import CountingMatroid.Analysis.RestartDrawProbe

set_option autoImplicit false

/-!
Return-level abort attribution for one capped return scan. A return either
reaches a non-invalid continuing state, exhausts the shared attempt cap, or
aborts at a draw whose descriptor is captured by a concrete sticky probe
with the right ordinal. A probe whose ordinal is at least the return's final
count cannot be disturbed by this return's own processing.
-/
namespace CountingMatroid.Analysis.RestartReturnAbortAttribution

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Unfold one step of a capped-cost `foldlWhile`. -/
private theorem foldlWhile_cons_val {α β : Type}
    (f : β → α → Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell (Option β))
    (a : α) (l : List α) (b : β) :
    (Arlib.Computation.Charged.foldlWhile f (a :: l) b).val =
      match (f b a).val with
      | none => b
      | some b' => (Arlib.Computation.Charged.foldlWhile f l b').val := by
  cases hf : (f b a).val with
  | none =>
    simp only [Arlib.Computation.Charged.val] at hf ⊢
    simp only [Arlib.Computation.Charged.foldlWhile, hf]
  | some b' =>
    simp only [Arlib.Computation.Charged.val] at hf ⊢
    simp only [Arlib.Computation.Charged.foldlWhile, hf]

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)

/-- INTERNAL: The raw (uninstrumented) return scan over an arbitrary list and
starting accumulator. -/
noncomputable def rawScan (xs : List ℕ) (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    (Option (RestartCursor n) × Bool) × ℕ :=
  (Arlib.Computation.Charged.foldlWhile
    (fun acc (_ : ℕ) => countedBody r o₁ o₂ tape s q w acc) xs acc).val

/-- INTERNAL: The probed return scan over an arbitrary list, at a fixed
ordinal and draw index, and starting accumulator. -/
noncomputable def probedScan (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ) :=
  (Arlib.Computation.Charged.foldlWhile
    (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs acc).val

theorem rawScan_nil (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    rawScan r o₁ o₂ tape s q w [] acc = acc := rfl

theorem probedScan_nil (ordinal : ℕ) (draw : Fin 3)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    probedScan r o₁ o₂ tape s q w ordinal draw [] acc = acc := rfl

theorem rawScan_cons (a : ℕ) (xs : List ℕ) (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    rawScan r o₁ o₂ tape s q w (a :: xs) acc =
      match (countedBody r o₁ o₂ tape s q w acc).val with
      | none => acc
      | some next => rawScan r o₁ o₂ tape s q w xs next := by
  unfold rawScan
  rw [foldlWhile_cons_val (fun acc (_ : ℕ) => countedBody r o₁ o₂ tape s q w acc) a xs acc]
  cases (countedBody r o₁ o₂ tape s q w acc).val <;> rfl

/-- INTERNAL: One guarded step of `countedBody`, refused branch: the shared
cap has already been reached for this restart cursor. -/
private theorem countedBody_refused (current : RestartCursor n) (count : ℕ)
    (hcap : ¬ current.attempts < s.restartCap) :
    (countedBody r o₁ o₂ tape s q w ((some current, false), count)).val =
      some ((none, true), count) := by
  unfold countedBody traceBody attemptIncrement Model.Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, apply_ite Arlib.Computation.Charged.val, decide_eq_true_eq,
    Bool.false_eq_true, if_false, if_neg hcap, Option.map_some, Nat.add_zero]

/-- INTERNAL: One guarded step of `countedBody`, allowed branch: the actual
chain attempt either aborts or lands on a classified continuing state. -/
private theorem countedBody_allowed (current : RestartCursor n) (count : ℕ)
    (hallow : current.attempts < s.restartCap) :
    (countedBody r o₁ o₂ tape s q w ((some current, false), count)).val =
      match (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
      | none => some ((none, true), count + 1)
      | some (state, bitCursor) =>
          some ((some ⟨state, bitCursor, current.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1) := by
  unfold countedBody traceBody attemptIncrement Model.Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, apply_ite Arlib.Computation.Charged.val, decide_eq_true_eq,
    Bool.false_eq_true, if_false, if_pos hallow]
  cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
  | none => simp [hcs]
  | some result =>
    obtain ⟨state, bitCursor⟩ := result
    simp only [hcs, Arlib.Computation.Charged.val_bind]
    cases hk : (classifyState state).val with
    | invalid => simp [hk, Model.Operations.successor, Arlib.Computation.Charged.val_op]
    | transversal => simp [hk, Model.Operations.successor, Arlib.Computation.Charged.val_op]
    | defect i j => simp [hk, Model.Operations.successor, Arlib.Computation.Charged.val_op]

/-- INTERNAL: `probedBody` from a fresh observation is `countedBody` paired
with the matching capture site. -/
private theorem probedBody_val (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × Bool) × ℕ) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (acc, none)).val =
      (countedBody r o₁ o₂ tape s q w acc).val.map
        (fun result => (result, bodySite r o₁ o₂ tape s q w ordinal draw acc)) := by
  unfold probedBody
  simp only [Option.none_or, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]

/-- INTERNAL: An unmatched ordinal captures nothing. -/
private theorem bodySite_ne (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n)
    (count : ℕ) (hne : count ≠ ordinal) :
    bodySite r o₁ o₂ tape s q w ordinal draw ((some current, false), count) = none := by
  unfold bodySite
  simp only [hne, and_false, Bool.false_eq_true, if_false]

/-- INTERNAL: A matched, allowed ordinal captures exactly the chain's
pre-draw site. -/
private theorem bodySite_eq (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n)
    (hallow : current.attempts < s.restartCap) :
    bodySite r o₁ o₂ tape s q w ordinal draw ((some current, false), ordinal) =
      chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw := by
  unfold bodySite
  simp only [hallow, true_and, Bool.false_eq_true, if_false, if_true]

theorem probedScan_cons (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    probedScan r o₁ o₂ tape s q w ordinal draw (a :: xs) acc =
      match (probedBody r o₁ o₂ tape s q w ordinal draw acc).val with
      | none => acc
      | some next => probedScan r o₁ o₂ tape s q w ordinal draw xs next := by
  unfold probedScan
  rw [foldlWhile_cons_val
    (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) a xs acc]
  cases (probedBody r o₁ o₂ tape s q w ordinal draw acc).val <;> rfl

/-- INTERNAL: A done, aborted accumulator is absorbing for `countedBody`. -/
private theorem countedBody_done (st : Option (RestartCursor n)) (cnt : ℕ) :
    (countedBody r o₁ o₂ tape s q w ((st, true), cnt)).val = none := by
  unfold countedBody traceBody
  simp

/-- INTERNAL: A done accumulator is absorbing for `probedBody`, regardless
of the underlying state, ordinal, draw, or prior observation. -/
private theorem probedBody_done (st : Option (RestartCursor n)) (ordinal : ℕ) (draw : Fin 3)
    (cnt : ℕ) (observed : Option (ℕ × ℕ)) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((st, true), cnt), observed)).val = none := by
  unfold probedBody
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    countedBody_done, Option.map_none]

/-- INTERNAL: Once done, no further elements of the list change the raw
accumulator, whatever the underlying state. -/
theorem rawScan_done (st : Option (RestartCursor n)) (xs : List ℕ) (cnt : ℕ) :
    rawScan r o₁ o₂ tape s q w xs ((st, true), cnt) = ((st, true), cnt) := by
  cases xs with
  | nil => rw [rawScan_nil]
  | cons a xs => rw [rawScan_cons, countedBody_done]

/-- INTERNAL: Once done, no further elements of the list change the probed
accumulator, regardless of the underlying state, ordinal, draw, or
observation. -/
theorem probedScan_done (st : Option (RestartCursor n)) (ordinal : ℕ) (draw : Fin 3)
    (xs : List ℕ) (cnt : ℕ) (observed : Option (ℕ × ℕ)) :
    probedScan r o₁ o₂ tape s q w ordinal draw xs (((st, true), cnt), observed) =
      (((st, true), cnt), observed) := by
  cases xs with
  | nil => rw [probedScan_nil]
  | cons a xs => rw [probedScan_cons, probedBody_done]

/-- INTERNAL: One refused step, folded into the next element's `rawScan`. -/
private theorem rawScan_cons_refused (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (hcap : ¬ current.attempts < s.restartCap) :
    rawScan r o₁ o₂ tape s q w (a :: xs) ((some current, false), count) =
      rawScan r o₁ o₂ tape s q w xs ((none, true), count) := by
  rw [rawScan_cons, countedBody_refused r o₁ o₂ tape s q w current count hcap]

/-- INTERNAL: One aborted step, folded into the next element's `rawScan`. -/
private theorem rawScan_cons_abort (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (hallow : current.attempts < s.restartCap)
    (hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
      none) :
    rawScan r o₁ o₂ tape s q w (a :: xs) ((some current, false), count) =
      rawScan r o₁ o₂ tape s q w xs ((none, true), count + 1) := by
  rw [rawScan_cons, countedBody_allowed r o₁ o₂ tape s q w current count hallow, hcs]

/-- INTERNAL: One successful step, folded into the next element's `rawScan`. -/
private theorem rawScan_cons_success (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (hallow : current.attempts < s.restartCap) (state : PairedSet n)
    (bitCursor : ℕ)
    (hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
      some (state, bitCursor)) :
    rawScan r o₁ o₂ tape s q w (a :: xs) ((some current, false), count) =
      rawScan r o₁ o₂ tape s q w xs
        ((some ⟨state, bitCursor, current.attempts + 1⟩,
          decide ((classifyState state).val = StateKind.transversal)), count + 1) := by
  rw [rawScan_cons, countedBody_allowed r o₁ o₂ tape s q w current count hallow, hcs]

/-- INTERNAL: One unmatched, refused step, folded into the next element's
`probedScan`. -/
private theorem probedScan_cons_ne_refused (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (ordinal : ℕ) (draw : Fin 3) (hne : count ≠ ordinal)
    (hcap : ¬ current.attempts < s.restartCap) :
    probedScan r o₁ o₂ tape s q w ordinal draw (a :: xs)
        (((some current, false), count), none) =
      probedScan r o₁ o₂ tape s q w ordinal draw xs (((none, true), count), none) := by
  rw [probedScan_cons, probedBody_val, countedBody_refused r o₁ o₂ tape s q w current count
    hcap, bodySite_ne r o₁ o₂ tape s q w ordinal draw current count hne]
  rfl

/-- INTERNAL: One unmatched, aborting step, folded into the next element's
`probedScan`. -/
private theorem probedScan_cons_ne_abort (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (ordinal : ℕ) (draw : Fin 3) (hne : count ≠ ordinal)
    (hallow : current.attempts < s.restartCap)
    (hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
      none) :
    probedScan r o₁ o₂ tape s q w ordinal draw (a :: xs)
        (((some current, false), count), none) =
      probedScan r o₁ o₂ tape s q w ordinal draw xs (((none, true), count + 1), none) := by
  rw [probedScan_cons, probedBody_val, countedBody_allowed r o₁ o₂ tape s q w current count
    hallow, hcs, bodySite_ne r o₁ o₂ tape s q w ordinal draw current count hne]
  rfl

/-- INTERNAL: One unmatched, successful step, folded into the next element's
`probedScan`. -/
private theorem probedScan_cons_ne_success (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (ordinal : ℕ) (draw : Fin 3) (hne : count ≠ ordinal)
    (hallow : current.attempts < s.restartCap) (state : PairedSet n) (bitCursor : ℕ)
    (hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
      some (state, bitCursor)) :
    probedScan r o₁ o₂ tape s q w ordinal draw (a :: xs)
        (((some current, false), count), none) =
      probedScan r o₁ o₂ tape s q w ordinal draw xs
        ((((some ⟨state, bitCursor, current.attempts + 1⟩,
            decide ((classifyState state).val = StateKind.transversal))), count + 1), none) := by
  rw [probedScan_cons, probedBody_val, countedBody_allowed r o₁ o₂ tape s q w current count
    hallow, hcs, bodySite_ne r o₁ o₂ tape s q w ordinal draw current count hne]
  rfl

/-- INTERNAL: One matched, allowed, aborting step actually captures. -/
private theorem probedScan_cons_capture (a : ℕ) (xs : List ℕ) (current : RestartCursor n)
    (count : ℕ) (draw : Fin 3) (hallow : current.attempts < s.restartCap)
    (hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val =
      none) (d : ℕ × ℕ)
    (hsite : chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw = some d) :
    probedScan r o₁ o₂ tape s q w count draw (a :: xs)
        (((some current, false), count), none) =
      probedScan r o₁ o₂ tape s q w count draw xs (((none, true), count + 1), some d) := by
  rw [probedScan_cons, probedBody_val, countedBody_allowed r o₁ o₂ tape s q w current count
    hallow, hcs, bodySite_eq r o₁ o₂ tape s q w count draw current hallow, hsite]
  rfl

/-- INTERNAL: Positivity/attribution target for one capped return scan,
generalized over an arbitrary remaining list and starting accumulator. -/
theorem returnScan_attr :
    ∀ (xs : List ℕ) (current : RestartCursor n) (count : ℕ),
      (classifyState current.state).val ≠ .invalid → current.attempts = count →
      count ≤ (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).2 ∧
      ((∃ final : RestartCursor n,
          (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).1.1 = some final ∧
          (classifyState final.state).val ≠ .invalid ∧
          final.attempts = (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).2 ∧
          (¬ (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).1.2 →
            (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).2 = count + xs.length) ∧
          ∀ ordinal (draw : Fin 3),
            (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).2 ≤ ordinal →
            probedScan r o₁ o₂ tape s q w ordinal draw xs (((some current, false), count), none) =
              (rawScan r o₁ o₂ tape s q w xs ((some current, false), count), none))
        ∨ ((rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).1.1 = none ∧
            (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).1.2 = true ∧
            s.restartCap ≤ (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).2)
        ∨ ((rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).1.1 = none ∧
            (rawScan r o₁ o₂ tape s q w xs ((some current, false), count)).1.2 = true ∧
            ∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧
              ordinal < s.restartCap ∧
              (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
              (probedScan r o₁ o₂ tape s q w ordinal draw xs
                (((some current, false), count), none)).2 = some d)) := by
  intro xs
  induction xs with
  | nil =>
    intro current count hvalid hinv
    rw [rawScan_nil]
    refine ⟨le_refl _, Or.inl ⟨current, rfl, hvalid, hinv, ?_, ?_⟩⟩
    · intro; rfl
    · intro ordinal draw _
      rw [probedScan_nil]
  | cons a xs ih =>
    intro current count hvalid hinv
    by_cases hallow : current.attempts < s.restartCap
    · cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w
          current.state current.bitCursor).val with
      | none =>
        -- Draw-abort at this ordinal: capture it directly.
        obtain ⟨site, d, hsite, hfail⟩ :=
          chain_abort_draw_site r o₁ o₂ tape s q w current.state current.bitCursor hvalid hcs
        rw [rawScan_cons_abort r o₁ o₂ tape s q w a xs current count hallow hcs,
          rawScan_done]
        refine ⟨by omega, Or.inr (Or.inr ⟨rfl, rfl, count, site, d, le_refl _, hinv ▸ hallow,
          hfail, ?_⟩)⟩
        rw [probedScan_cons_capture r o₁ o₂ tape s q w a xs current count site hallow hcs d
          hsite, probedScan_done]
      | some result =>
        obtain ⟨state, bitCursor⟩ := result
        have hnewvalid : (classifyState state).val ≠ .invalid :=
          ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ tape s.drawTrials q w
            current.state current.bitCursor (state, bitCursor) hvalid hcs
        rw [rawScan_cons_success r o₁ o₂ tape s q w a xs current count hallow state bitCursor
          hcs]
        by_cases hkind : (classifyState state).val = StateKind.transversal
        · -- Reached a transversal: this return is a sticky success.
          have hbool : decide ((classifyState state).val = StateKind.transversal) = true := by
            simp [hkind]
          rw [hbool, rawScan_done]
          refine ⟨by omega, Or.inl ⟨⟨state, bitCursor, current.attempts + 1⟩, rfl, hnewvalid,
            congrArg (· + 1) hinv, ?_, ?_⟩⟩
          · intro h; exact absurd rfl h
          · intro ordinal draw _
            rw [probedScan_cons_ne_success r o₁ o₂ tape s q w a xs current count ordinal draw
              (by omega) hallow state bitCursor hcs, hbool, probedScan_done]
        · have hbool : decide ((classifyState state).val = StateKind.transversal) = false := by
            simp [hkind]
          rw [hbool]
          have hnextinv : (⟨state, bitCursor, current.attempts + 1⟩ : RestartCursor n).attempts
              = count + 1 := by simp [hinv]
          obtain ⟨hle, hcases⟩ :=
            ih ⟨state, bitCursor, current.attempts + 1⟩ (count + 1) hnewvalid hnextinv
          refine ⟨by omega, ?_⟩
          rcases hcases with ⟨final, hfinal1, hfinal2, hfinal3, hfinal4, hfinal5⟩
            | ⟨hcapped1, hcapped1b, hcapped2⟩
            | ⟨habort1, habort1b, ordinal, draw, d, hge, hcapord, hfail, hcap⟩
          · refine Or.inl ⟨final, hfinal1, hfinal2, hfinal3, ?_, ?_⟩
            · intro h
              rw [List.length_cons, hfinal4 h]
              omega
            intro ordinal draw hord
            rw [probedScan_cons_ne_success r o₁ o₂ tape s q w a xs current count ordinal draw
              (by omega) hallow state bitCursor hcs, hbool]
            exact hfinal5 ordinal draw hord
          · exact Or.inr (Or.inl ⟨hcapped1, hcapped1b, hcapped2⟩)
          · refine Or.inr (Or.inr ⟨habort1, habort1b, ordinal, draw, d, by omega, hcapord, hfail,
              ?_⟩)
            rw [probedScan_cons_ne_success r o₁ o₂ tape s q w a xs current count ordinal draw
              (by omega) hallow state bitCursor hcs, hbool]
            exact hcap
    · rw [rawScan_cons_refused r o₁ o₂ tape s q w a xs current count hallow, rawScan_done]
      refine ⟨by omega, Or.inr (Or.inl ⟨rfl, rfl, by omega⟩)⟩

/-- INTERNAL: `countedReturn`'s public value in terms of `rawScan` over the
actual restart cap. -/
private theorem countedReturn_eq (start : RestartCursor n) (count : ℕ) :
    (countedReturn r o₁ o₂ tape s q w start count).val =
      (let raw := rawScan r o₁ o₂ tape s q w (List.range s.restartCap)
        ((some start, false), count)
       (if raw.1.2 then raw.1.1 else none, raw.2)) := by
  unfold countedReturn rawScan Arlib.Computation.Charged.repeatWhile
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]

/-- INTERNAL: `probedReturn`'s public value in terms of `probedScan` over the
actual restart cap. -/
private theorem probedReturn_eq (ordinal : ℕ) (draw : Fin 3) (start : RestartCursor n)
    (count : ℕ) (observed : Option (ℕ × ℕ)) :
    (probedReturn r o₁ o₂ tape s q w ordinal draw start count observed).val =
      (let probed := probedScan r o₁ o₂ tape s q w ordinal draw (List.range s.restartCap)
        (((some start, false), count), observed)
       ((if probed.1.1.2 then probed.1.1.1 else none, probed.1.2), probed.2)) := by
  unfold probedReturn probedScan Arlib.Computation.Charged.repeatWhile
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure]

/-- One capped return scan either reaches a non-invalid continuing state,
exhausts the shared restart cap, or aborts at a draw whose descriptor is
captured by the concrete sticky probe at the matching ordinal. A probe at
or beyond the return's final count is never disturbed by this return.
PAPER: main.tex:1163-1176,1392-1421 -/
theorem return_attribution (start : RestartCursor n) (count : ℕ)
    (hvalid : (classifyState start.state).val ≠ .invalid) (hinv : start.attempts = count) :
    count ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
    ((∃ final : RestartCursor n,
        (countedReturn r o₁ o₂ tape s q w start count).val.1 = some final ∧
        (classifyState final.state).val ≠ .invalid ∧
        final.attempts = (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
        ∀ ordinal (draw : Fin 3),
          (countedReturn r o₁ o₂ tape s q w start count).val.2 ≤ ordinal →
          (probedReturn r o₁ o₂ tape s q w ordinal draw start count none).val =
            ((countedReturn r o₁ o₂ tape s q w start count).val, none))
      ∨ (s.restartCap ≤ (countedReturn r o₁ o₂ tape s q w start count).val.2 ∧
          (countedReturn r o₁ o₂ tape s q w start count).val.1 = none)
      ∨ (∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧ ordinal < s.restartCap ∧
          (countedReturn r o₁ o₂ tape s q w start count).val.1 = none ∧
          (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
          (probedReturn r o₁ o₂ tape s q w ordinal draw start count none).val.2 = some d)) := by
  obtain ⟨hle, hcases⟩ := returnScan_attr r o₁ o₂ tape s q w (List.range s.restartCap) start
    count hvalid hinv
  rw [countedReturn_eq]
  dsimp only
  rcases hcases with ⟨final, hfinal1, hfinal2, hfinal3, hfinal4, hfinal5⟩
    | ⟨hcapped1, hcapped1b, hcapped2⟩
    | ⟨habort1, habort1b, ordinal, draw, d, hge, hcapord, hfail, hcap⟩
  · by_cases hdone : (rawScan r o₁ o₂ tape s q w (List.range s.restartCap)
        ((some start, false), count)).1.2
    · refine ⟨hle, Or.inl ⟨final, by simp [hdone, hfinal1], hfinal2, by simp [hfinal3], ?_⟩⟩
      intro ordinal draw hord
      rw [probedReturn_eq, hfinal5 ordinal draw (by simpa using hord)]
    · have hlen : (rawScan r o₁ o₂ tape s q w (List.range s.restartCap)
          ((some start, false), count)).2 = count + s.restartCap := by
        rw [hfinal4 hdone, List.length_range]
      exact ⟨hle, Or.inr (Or.inl ⟨by omega, by simp [hdone]⟩)⟩
  · refine ⟨hle, Or.inr (Or.inl ⟨hcapped2, ?_⟩)⟩
    simp [hcapped1b, hcapped1]
  · refine ⟨hle, Or.inr (Or.inr ⟨ordinal, draw, d, hge, hcapord, by simp [habort1b, habort1],
      hfail,
      ?_⟩)⟩
    rw [probedReturn_eq]
    simp [hcap]

end CountingMatroid.Analysis.RestartReturnAbortAttribution
