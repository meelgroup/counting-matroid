import CountingMatroid.Analysis.RestartDrawProbe

set_option autoImplicit false

/-!
Interval replay for the concrete ordinal probe's own accumulation, confined
to one capped return scan and lifted through the transition, stage and
restart folds. A captured descriptor can only ever change at the globally
unique attempt whose running count matches the probed ordinal; before that
attempt the probe is silent, and after it the descriptor is sticky.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeScanReplay
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Analysis.RestartAttemptAccounting

/-- INTERNAL: Once a charged `foldlWhile` accumulator's side observation is
fixed, it survives every further step of that fold. -/
private theorem charged_foldlWhile_sticky {X D α : Type}
    (g : (X × Option D) → α → Arlib.Computation.Charged Operations.Op Operations.Cell
      (Option (X × Option D)))
    (d : D) (hsticky : ∀ x a y, (g (x, some d) a).val = some y → y.2 = some d)
    (xs : List α) (x0 : X) :
    (Arlib.Computation.Charged.foldlWhile g xs (x0, some d)).val.2 = some d := by
  induction xs generalizing x0 with
  | nil => rfl
  | cons a xs ih =>
    cases hg : (g (x0, some d) a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at hg ⊢
      simp only [Arlib.Computation.Charged.foldlWhile, hg]
    | some y =>
      have hy := hsticky x0 a y hg
      obtain ⟨x1, ob1⟩ := y
      simp only at hy
      subst hy
      have hi := ih x1
      simp only [Arlib.Computation.Charged.val] at hg hi ⊢
      simpa only [Arlib.Computation.Charged.foldlWhile, hg] using hi

/-- INTERNAL: Once a charged `foldl` accumulator's side observation is fixed,
it survives every further step of that fold. -/
private theorem charged_foldl_sticky {X D α : Type}
    (g : (X × Option D) → α → Arlib.Computation.Charged Operations.Op Operations.Cell
      (X × Option D))
    (d : D) (hsticky : ∀ x a, (g (x, some d) a).val.2 = some d)
    (xs : List α) (x0 : X) :
    (Arlib.Computation.Charged.foldl g xs (x0, some d)).val.2 = some d := by
  induction xs generalizing x0 with
  | nil => rfl
  | cons a xs ih =>
    rw [Arlib.Computation.Charged.val_foldl_cons]
    have h1 := hsticky x0 a
    cases hx : (g (x0, some d) a).val with
    | mk x1 ob1 =>
      simp only [hx] at h1
      subst h1
      exact ih x1

/-- INTERNAL: Unfold one step of the probe's own capped-cost `foldlWhile`. -/
private theorem probedBody_scan_cons {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)) :
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) (a :: xs) acc).val =
      match (probedBody r o₁ o₂ tape s q w ordinal draw acc).val with
      | none => acc
      | some next =>
          (Arlib.Computation.Charged.foldlWhile
            (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs next).val := by
  cases hf : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val with
  | none =>
    simp only [Arlib.Computation.Charged.val] at hf ⊢
    simp only [Arlib.Computation.Charged.foldlWhile, hf]
  | some next =>
    simp only [Arlib.Computation.Charged.val] at hf ⊢
    simp only [Arlib.Computation.Charged.foldlWhile, hf]

/-- INTERNAL: Once the probe has captured a descriptor, it is retained
through any remaining elements of the probe's own return-scan fold. -/
theorem probedBody_scan_sticky {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc1 : (Option (RestartCursor n) × Bool) × ℕ) (d : ℕ × ℕ) :
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
        (acc1, some d)).val.2 = some d := by
  apply charged_foldlWhile_sticky
  intro x a y h
  simp only [probedBody, Arlib.Computation.Charged.val_bind,
    Arlib.Computation.Charged.val_pure, Option.some_or, Option.map_eq_some_iff] at h
  obtain ⟨result, _, h⟩ := h
  cases h
  rfl

/-- INTERNAL: A done accumulator is absorbing for the probe's body,
regardless of the underlying state, ordinal, draw, or prior observation. -/
private theorem probedBody_done {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (st : Option (RestartCursor n)) (count : ℕ) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((st, true), count), none)).val = none := by
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
  simp

/-- INTERNAL: A dead accumulator is absorbing for the probe's body,
regardless of the done flag, ordinal, draw, or prior observation. -/
private theorem probedBody_dead {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (done : Bool) (count : ℕ) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((none, done), count), none)).val = none := by
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
  cases done <;> simp

/-- INTERNAL: One guarded, allowed step of the probe's body, refused branch:
the shared restart cap has already been reached for this cursor. -/
private theorem probedBody_refused {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n) (count : ℕ)
    (hcap : ¬ current.attempts < s.restartCap) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((some current, false), count), none)).val =
      some (((none, true), count), none) := by
  have hcap' : ¬ (current.attempts < s.restartCap ∧ count = ordinal) := fun h => hcap h.1
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
    bodySite RestartAttemptAccounting.attemptIncrement Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, decide_eq_true_eq,
    Bool.false_eq_true, if_false, if_neg hcap, if_neg hcap',
    Option.map_some, Nat.add_zero, Option.none_or]

/-- INTERNAL: One guarded, allowed, ordinal-mismatched step of the probe's
body: the actual chain attempt proceeds and the probe captures nothing. -/
private theorem probedBody_ne {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n) (count : ℕ)
    (hallow : current.attempts < s.restartCap) (hne : count ≠ ordinal) :
    (probedBody r o₁ o₂ tape s q w ordinal draw (((some current, false), count), none)).val =
      match (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
      | none => some (((none, true), count + 1), none)
      | some (state, bitCursor) =>
          some (((some ⟨state, bitCursor, current.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1), none) := by
  have hne' : ¬ (current.attempts < s.restartCap ∧ count = ordinal) := fun h => hne h.2
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
    bodySite RestartAttemptAccounting.attemptIncrement Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, decide_eq_true_eq,
    Bool.false_eq_true, if_false, if_pos hallow, if_neg hne', Option.none_or]
  cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
  | none => simp
  | some result =>
    obtain ⟨state, bitCursor⟩ := result
    simp only [Arlib.Computation.Charged.val_bind]
    cases hk : (classifyState state).val with
    | invalid => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | transversal => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | defect i j => simp [Operations.successor, Arlib.Computation.Charged.val_op]

/-- INTERNAL: One guarded, allowed, ordinal-matched step of the probe's
body: the probe observes exactly the chain's pre-draw site. -/
private theorem probedBody_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (draw : Fin 3) (current : RestartCursor n) (count : ℕ)
    (hallow : current.attempts < s.restartCap) :
    (probedBody r o₁ o₂ tape s q w count draw (((some current, false), count), none)).val =
      match (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
      | none => some (((none, true), count + 1),
          chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw)
      | some (state, bitCursor) =>
          some (((some ⟨state, bitCursor, current.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1),
            chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw) := by
  unfold probedBody RestartAttemptAccounting.countedBody RestartAttemptAccounting.traceBody
    bodySite RestartAttemptAccounting.attemptIncrement Operations.lessThan
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    Arlib.Computation.Charged.val_op, decide_eq_true_eq,
    Bool.false_eq_true, if_false, and_true, if_pos hallow, Option.none_or]
  cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state current.bitCursor).val with
  | none => simp
  | some result =>
    obtain ⟨state, bitCursor⟩ := result
    simp only [Arlib.Computation.Charged.val_bind]
    cases hk : (classifyState state).val with
    | invalid => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | transversal => simp [Operations.successor, Arlib.Computation.Charged.val_op]
    | defect i j => simp [Operations.successor, Arlib.Computation.Charged.val_op]

/-- INTERNAL: Scanning from a dead or already-done accumulator never
captures anything, for any remaining list. -/
private theorem probedBody_scan_frozen {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) (st : Option (RestartCursor n))
    (done : Bool) (count : ℕ) (hfr : st = none ∨ done = true) :
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
        (((st, done), count), none)).val.2 = none := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    rw [probedBody_scan_cons]
    rcases hfr with hfr | hfr
    · subst hfr
      rw [probedBody_dead]
    · subst hfr
      rw [probedBody_done]

/-- INTERNAL: Scanning from a running count already past the probed ordinal,
with nothing captured yet, never captures anything. -/
theorem probedBody_scan_past {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) :
    ∀ (acc1 : Option (RestartCursor n) × Bool) (count : ℕ), ordinal < count →
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
        ((acc1, count), none)).val.2 = none := by
  induction xs with
  | nil => intro acc1 count _; rfl
  | cons a xs ih =>
    intro acc1 count hlt
    obtain ⟨cur, done⟩ := acc1
    cases done with
    | true =>
      exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) cur true
        count (Or.inr rfl)
    | false =>
      cases cur with
      | none =>
        exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) none
          false count (Or.inl rfl)
      | some current =>
        by_cases hallow : current.attempts < s.restartCap
        · rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw current
            count hallow (by omega)]
          cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
              current.bitCursor).val with
          | none =>
            simp only
            exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw xs none true
              (count + 1) (Or.inl rfl)
          | some result =>
            obtain ⟨state, bitCursor⟩ := result
            simp only
            exact ih _ (count + 1) (by omega)
        · rw [probedBody_scan_cons, probedBody_refused r o₁ o₂ tape s q w ordinal draw current
            count hallow]
          simp only
          exact probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw xs none true count
            (Or.inl rfl)

/-- INTERNAL: Interval replay for the probe's own capped return scan, from a
fresh observation. A captured descriptor arises only at the globally unique
attempt whose running count matches the probed ordinal, so it can only read
tape bits from the floor of the entering cursor up to its own cursor.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem probedBody_scan_replay {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3) :
    ∀ (xs : List ℕ) (acc1 : Option (RestartCursor n) × Bool) (count floor : ℕ),
      (∀ cur, acc1.1 = some cur → floor ≤ cur.bitCursor) →
      ChainStepIntervalReplay.SuccessReplay
        (fun tape => (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          ((acc1, count), none)).val.2)
        Prod.fst floor := by
  intro xs
  induction xs with
  | nil =>
    intro acc1 count floor _ tape out h
    cases h
  | cons a xs ih =>
    intro acc1 count floor hfloor tape out h
    dsimp only at h
    dsimp only
    obtain ⟨cur1, done1⟩ := acc1
    cases done1 with
    | true =>
      rw [probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) cur1 true count
        (Or.inr rfl)] at h
      cases h
    | false =>
      cases cur1 with
      | none =>
        rw [probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw (a :: xs) none false count
          (Or.inl rfl)] at h
        cases h
      | some current =>
        have hfl : floor ≤ current.bitCursor := hfloor current rfl
        by_cases hallow : current.attempts < s.restartCap
        · by_cases hcm : count = ordinal
          · subst hcm
            have key : ∀ (tp : ℕ → Bool) (d : ℕ × ℕ),
                chainDrawSite r o₁ o₂ tp s q w current.state current.bitCursor draw = some d →
                (Arlib.Computation.Charged.foldlWhile
                  (fun acc (_ : ℕ) => probedBody r o₁ o₂ tp s q w count draw acc) (a :: xs)
                  (((some current, false), count), none)).val.2 = some d := by
              intro tp d hd
              rw [probedBody_scan_cons, probedBody_eq r o₁ o₂ tp s q w draw current count hallow]
              cases hcs : (chainStep r o₁ o₂ tp s.drawTrials q w current.state
                  current.bitCursor).val with
              | none =>
                simp only
                rw [hd]
                exact probedBody_scan_sticky r o₁ o₂ tp s q w count draw xs _ d
              | some result =>
                obtain ⟨state, bitCursor⟩ := result
                simp only
                rw [hd]
                exact probedBody_scan_sticky r o₁ o₂ tp s q w count draw xs _ d
            cases hsite0 : chainDrawSite r o₁ o₂ tape s q w current.state current.bitCursor draw with
            | none =>
              exfalso
              rw [probedBody_scan_cons, probedBody_eq r o₁ o₂ tape s q w draw current count
                hallow] at h
              cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
                  current.bitCursor).val with
              | none =>
                rw [hcs, hsite0] at h
                simp only at h
                rw [probedBody_scan_frozen r o₁ o₂ tape s q w count draw xs none true
                  (count + 1) (Or.inl rfl)] at h
                cases h
              | some result =>
                obtain ⟨state, bitCursor⟩ := result
                rw [hcs, hsite0] at h
                simp only at h
                rw [probedBody_scan_past r o₁ o₂ tape s q w count draw xs _ (count + 1)
                  (Nat.lt_succ_self count)] at h
                cases h
            | some d =>
              have h0 := h
              rw [key tape d hsite0] at h0
              have hd : d = out := Option.some.inj h0
              subst hd
              have hsite := chainDrawSite_success_interval r o₁ o₂ s q w current.state
                current.bitCursor draw tape d hsite0
              refine ⟨hfl.trans hsite.1, ?_⟩
              intro other hagree
              exact key other d (hsite.2 other (fun i hlo hhi => hagree i (hfl.trans hlo) hhi))
          · rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw current
              count hallow hcm] at h
            cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w current.state
                current.bitCursor).val with
            | none =>
              rw [hcs] at h
              simp only at h
              rw [probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw xs none true
                (count + 1) (Or.inl rfl)] at h
              cases h
            | some result =>
              obtain ⟨state, bitCursor⟩ := result
              rw [hcs] at h
              simp only at h
              have hstep := chainStep_success_interval r o₁ o₂ s.drawTrials q w current.state
                current.bitCursor tape (state, bitCursor) hcs
              have hr := ih (some ⟨state, bitCursor, current.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)) (count + 1)
                bitCursor (fun cur hcur => by
                  have hc := Option.some.inj hcur
                  subst hc
                  exact le_refl _)
                tape out h
              refine ⟨hfl.trans (hstep.1.trans hr.1), ?_⟩
              intro other hagree
              have heqstep := hstep.2 other (fun i hlo hhi =>
                hagree i (hfl.trans hlo) (hhi.trans_le hr.1))
              have heqrest := hr.2 other (fun i hlo hhi =>
                hagree i (hfl.trans (hstep.1.trans hlo)) hhi)
              beta_reduce at heqstep heqrest ⊢
              rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ other s q w ordinal draw current
                count hallow hcm, heqstep]
              exact heqrest
        · rw [probedBody_scan_cons, probedBody_refused r o₁ o₂ tape s q w ordinal draw current
            count hallow] at h
          rw [probedBody_scan_frozen r o₁ o₂ tape s q w ordinal draw xs none true (count)
            (Or.inl rfl)] at h
          cases h

/-- INTERNAL: A dead or already-done accumulator leaves the whole scan value
unchanged, on every tape. -/
theorem probedBody_scan_frozen_val {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) (st : Option (RestartCursor n))
    (done : Bool) (count : ℕ) (hfr : st = none ∨ done = true) :
    (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
        (((st, done), count), none)).val = (((st, done), count), none) := by
  cases xs with
  | nil => rfl
  | cons a xs =>
    rw [probedBody_scan_cons]
    rcases hfr with hfr | hfr
    · subst hfr
      rw [probedBody_dead]
    · subst hfr
      rw [probedBody_done]

/-- INTERNAL: The retained attempt count never decreases along the probe's
return scan. -/
theorem probedBody_scan_count_mono {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) :
    ∀ (acc : ((Option (RestartCursor n) × Bool) × ℕ) × Option (ℕ × ℕ)),
    acc.1.2 ≤ (Arlib.Computation.Charged.foldlWhile
        (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs acc).val.1.2 := by
  induction xs with
  | nil => intro acc; exact le_refl _
  | cons a xs ih =>
    intro acc
    rw [probedBody_scan_cons]
    cases hb : (probedBody r o₁ o₂ tape s q w ordinal draw acc).val with
    | none => exact le_refl _
    | some next =>
      simp only
      refine le_trans ?_ (ih next)
      simp only [probedBody, RestartAttemptAccounting.countedBody,
        Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
        Option.map_map, Option.map_eq_some_iff] at hb
      obtain ⟨result, _, hb⟩ := hb
      subst hb
      exact Nat.le_add_right _ _

/-- INTERNAL: A return scan that captures nothing and ends live before the
probed ordinal replays its entire value from the bits its successful chain
attempts consumed; no attempt in it can have matched the ordinal.
TEXLINE: main.tex:1163-1176,1392-1421 -/
theorem probedBody_scan_quiet_replay {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n) (ordinal : ℕ) (draw : Fin 3) :
    ∀ (xs : List ℕ) (cur : RestartCursor n) (done : Bool) (count floor : ℕ),
      floor ≤ cur.bitCursor → ∀ (tape : ℕ → Bool) (c : RestartCursor n),
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.2 = none →
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.1.1.1 = some c →
      (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val.1.2 ≤ ordinal →
      floor ≤ c.bitCursor ∧ ∀ other : ℕ → Bool,
        (∀ i, floor ≤ i → i < c.bitCursor → tape i = other i) →
        (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ other s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val =
        (Arlib.Computation.Charged.foldlWhile
          (fun acc (_ : ℕ) => probedBody r o₁ o₂ tape s q w ordinal draw acc) xs
          (((some cur, done), count), none)).val := by
  intro xs
  induction xs with
  | nil =>
    intro cur done count floor hfl tape c _ hc _
    rw [Arlib.Computation.Charged.val_foldlWhile_nil] at hc
    have hc' : cur = c := Option.some.inj hc
    subst hc'
    refine ⟨hfl, fun other _ => ?_⟩
    rw [Arlib.Computation.Charged.val_foldlWhile_nil,
      Arlib.Computation.Charged.val_foldlWhile_nil]
  | cons a xs ih =>
    intro cur done count floor hfl tape c hobs hc hcount
    cases done with
    | true =>
      rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw _ _ true count
        (Or.inr rfl)] at hc
      have hc' : cur = c := Option.some.inj hc
      subst hc'
      refine ⟨hfl, fun other _ => ?_⟩
      rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw _ _ true count
        (Or.inr rfl), probedBody_scan_frozen_val r o₁ o₂ other s q w ordinal draw _ _ true
        count (Or.inr rfl)]
    | false =>
      by_cases hallow : cur.attempts < s.restartCap
      · by_cases hcm : count = ordinal
        · exfalso
          subst hcm
          rw [probedBody_scan_cons, probedBody_eq r o₁ o₂ tape s q w draw cur count
            hallow] at hcount
          cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w cur.state
              cur.bitCursor).val with
          | none =>
            rw [hcs] at hcount
            simp only at hcount
            have hm := probedBody_scan_count_mono r o₁ o₂ tape s q w count draw xs
              (((none, true), count + 1),
                chainDrawSite r o₁ o₂ tape s q w cur.state cur.bitCursor draw)
            simp only at hm
            omega
          | some result =>
            obtain ⟨state, bitCursor⟩ := result
            rw [hcs] at hcount
            simp only at hcount
            have hm := probedBody_scan_count_mono r o₁ o₂ tape s q w count draw xs
              (((some ⟨state, bitCursor, cur.attempts + 1⟩,
                decide ((classifyState state).val = StateKind.transversal)), count + 1),
                chainDrawSite r o₁ o₂ tape s q w cur.state cur.bitCursor draw)
            simp only at hm
            omega
        · rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w ordinal draw cur
            count hallow hcm] at hobs hc hcount
          cases hcs : (chainStep r o₁ o₂ tape s.drawTrials q w cur.state
              cur.bitCursor).val with
          | none =>
            rw [hcs] at hc
            simp only at hc
            rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw xs none true
              (count + 1) (Or.inl rfl)] at hc
            cases hc
          | some result =>
            obtain ⟨state, bitCursor⟩ := result
            rw [hcs] at hobs hc hcount
            simp only at hobs hc hcount
            have hstep := chainStep_success_interval r o₁ o₂ s.drawTrials q w cur.state
              cur.bitCursor tape (state, bitCursor) hcs
            have hr := ih ⟨state, bitCursor, cur.attempts + 1⟩
              (decide ((classifyState state).val = StateKind.transversal)) (count + 1)
              bitCursor (le_refl _) tape c hobs hc hcount
            refine ⟨hfl.trans (hstep.1.trans hr.1), ?_⟩
            intro other hagree
            have heqstep := hstep.2 other (fun i hlo hhi =>
              hagree i (hfl.trans hlo) (hhi.trans_le hr.1))
            have heqrest := hr.2 other (fun i hlo hhi =>
              hagree i (hfl.trans (hstep.1.trans hlo)) hhi)
            beta_reduce at heqstep heqrest ⊢
            rw [probedBody_scan_cons, probedBody_ne r o₁ o₂ other s q w ordinal draw cur
              count hallow hcm, heqstep, probedBody_scan_cons, probedBody_ne r o₁ o₂ tape s q w
              ordinal draw cur count hallow hcm, hcs]
            exact heqrest
      · rw [probedBody_scan_cons, probedBody_refused r o₁ o₂ tape s q w ordinal draw cur
          count hallow] at hc
        simp only at hc
        rw [probedBody_scan_frozen_val r o₁ o₂ tape s q w ordinal draw xs none true
          count (Or.inl rfl)] at hc
        cases hc

end CountingMatroid.Analysis.RestartDrawProbeScanReplay
