import CountingMatroid.Analysis.RestartReturnAbortAttribution

set_option autoImplicit false

/-!
Stage-level abort attribution for one stored-parameter stage. A stage either
reaches a non-invalid continuing state, exhausts the shared restart cap, or
aborts at a draw whose descriptor is captured by a concrete sticky probe at
the matching ordinal. A probe at or beyond the stage's final count is never
disturbed by this stage's own processing. This repeats the return-level
pattern one fold level up: `countedTransition`/`probedTransition` thread no
extra `Bool`, so the induction needs no guard case analysis of its own and
instead dispatches to `return_attribution` at each element.
-/
namespace CountingMatroid.Analysis.RestartStageAbortAttribution

open CountingMatroid.Model CountingMatroid.Program CountingMatroid.Model.Operations
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.RestartReturnAbortAttribution

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)

/-- INTERNAL: The raw (uninstrumented) stage scan over an arbitrary list and
starting accumulator. -/
noncomputable def rawStage (xs : List ℕ) (acc : Option (RestartCursor n) × ℕ) :
    Option (RestartCursor n) × ℕ :=
  (Arlib.Computation.Charged.foldl
    (fun acc (_ : ℕ) => countedTransition r o₁ o₂ tape s q w acc) xs acc).val

/-- INTERNAL: The probed stage scan over an arbitrary list, at a fixed
ordinal and draw index, and starting accumulator. -/
noncomputable def probedStageScan (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ) :=
  (Arlib.Computation.Charged.foldl
    (fun acc (_ : ℕ) => probedTransition r o₁ o₂ tape s q w ordinal draw acc) xs acc).val

theorem rawStage_nil (acc : Option (RestartCursor n) × ℕ) :
    rawStage r o₁ o₂ tape s q w [] acc = acc := rfl

theorem probedStageScan_nil (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw [] acc = acc := rfl

theorem rawStage_cons (a : ℕ) (xs : List ℕ) (acc : Option (RestartCursor n) × ℕ) :
    rawStage r o₁ o₂ tape s q w (a :: xs) acc =
      rawStage r o₁ o₂ tape s q w xs (countedTransition r o₁ o₂ tape s q w acc).val := by
  unfold rawStage
  rw [Arlib.Computation.Charged.val_foldl_cons]

theorem probedStageScan_cons (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw (a :: xs) acc =
      probedStageScan r o₁ o₂ tape s q w ordinal draw xs
        (probedTransition r o₁ o₂ tape s q w ordinal draw acc).val := by
  unfold probedStageScan
  rw [Arlib.Computation.Charged.val_foldl_cons]

/-- INTERNAL: A `none` state is absorbing for `countedTransition`. -/
private theorem countedTransition_none (cnt : ℕ) :
    (countedTransition r o₁ o₂ tape s q w (none, cnt)).val = (none, cnt) := rfl

/-- INTERNAL: A `none` state is absorbing for `probedTransition`, whatever
has already been observed. -/
private theorem probedTransition_none (ordinal : ℕ) (draw : Fin 3) (cnt : ℕ)
    (observed : Option (ℕ × ℕ)) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw ((none, cnt), observed)).val =
      ((none, cnt), observed) := rfl

/-- INTERNAL: A live state defers to `countedReturn`. -/
private theorem countedTransition_some (current : RestartCursor n) (cnt : ℕ) :
    (countedTransition r o₁ o₂ tape s q w (some current, cnt)).val =
      (countedReturn r o₁ o₂ tape s q w current cnt).val := rfl

/-- INTERNAL: A live state defers to `probedReturn`. -/
private theorem probedTransition_some (ordinal : ℕ) (draw : Fin 3) (current : RestartCursor n)
    (cnt : ℕ) (observed : Option (ℕ × ℕ)) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw ((some current, cnt), observed)).val =
      (probedReturn r o₁ o₂ tape s q w ordinal draw current cnt observed).val := rfl

/-- INTERNAL: Once aborted, no further elements of the list change the raw
accumulator. -/
theorem rawStage_done (xs : List ℕ) (cnt : ℕ) :
    rawStage r o₁ o₂ tape s q w xs (none, cnt) = (none, cnt) := by
  induction xs with
  | nil => rw [rawStage_nil]
  | cons a xs ih => rw [rawStage_cons, countedTransition_none]; exact ih

/-- INTERNAL: Once aborted, no further elements of the list change the
probed accumulator, whatever ordinal, draw or observation. -/
theorem probedStageScan_done (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) (cnt : ℕ)
    (observed : Option (ℕ × ℕ)) :
    probedStageScan r o₁ o₂ tape s q w ordinal draw xs ((none, cnt), observed) =
      ((none, cnt), observed) := by
  induction xs with
  | nil => rw [probedStageScan_nil]
  | cons a xs ih => rw [probedStageScan_cons, probedTransition_none]; exact ih

/-- INTERNAL: An already captured observation survives one further
`probedTransition`, whatever its underlying raw state. -/
private theorem probedTransition_observed_sticky (ordinal : ℕ) (draw : Fin 3)
    (acc : Option (RestartCursor n) × ℕ) (d : ℕ × ℕ) :
    (probedTransition r o₁ o₂ tape s q w ordinal draw (acc, some d)).val.2 = some d := by
  cases hc : acc.1 with
  | none => simp only [probedTransition, hc]; rfl
  | some current =>
    simp only [probedTransition, hc]
    exact RestartDrawProbe.probed_return_retains r o₁ o₂ tape s q w ordinal draw current
      acc.2 d

/-- INTERNAL: An already captured observation survives the whole remaining
stage, whatever its underlying raw state. -/
theorem probedStageScan_observed_sticky (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : Option (RestartCursor n) × ℕ) (d : ℕ × ℕ) :
    (probedStageScan r o₁ o₂ tape s q w ordinal draw xs (acc, some d)).2 = some d := by
  induction xs generalizing acc with
  | nil => rw [probedStageScan_nil]
  | cons a xs ih =>
    rw [probedStageScan_cons,
      show (probedTransition r o₁ o₂ tape s q w ordinal draw (acc, some d)).val =
        ((probedTransition r o₁ o₂ tape s q w ordinal draw (acc, some d)).val.1, some d) from
        Prod.ext rfl (probedTransition_observed_sticky r o₁ o₂ tape s q w ordinal draw acc d)]
    exact ih _

/-- INTERNAL: Positivity/attribution target for one stage scan, generalized
over an arbitrary remaining list and starting accumulator. -/
theorem stageScan_attr :
    ∀ (xs : List ℕ) (current : RestartCursor n) (count : ℕ),
      (classifyState current.state).val ≠ .invalid → current.attempts = count →
      count ≤ (rawStage r o₁ o₂ tape s q w xs (some current, count)).2 ∧
      ((∃ final : RestartCursor n,
          (rawStage r o₁ o₂ tape s q w xs (some current, count)).1 = some final ∧
          (classifyState final.state).val ≠ .invalid ∧
          final.attempts = (rawStage r o₁ o₂ tape s q w xs (some current, count)).2 ∧
          ∀ ordinal (draw : Fin 3),
            (rawStage r o₁ o₂ tape s q w xs (some current, count)).2 ≤ ordinal →
            probedStageScan r o₁ o₂ tape s q w ordinal draw xs ((some current, count), none) =
              (rawStage r o₁ o₂ tape s q w xs (some current, count), none))
        ∨ ((rawStage r o₁ o₂ tape s q w xs (some current, count)).1 = none ∧
            s.restartCap ≤ (rawStage r o₁ o₂ tape s q w xs (some current, count)).2)
        ∨ ((rawStage r o₁ o₂ tape s q w xs (some current, count)).1 = none ∧
            ∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧
              ordinal < s.restartCap ∧
              (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
              (probedStageScan r o₁ o₂ tape s q w ordinal draw xs
                ((some current, count), none)).2 = some d)) := by
  intro xs
  induction xs with
  | nil =>
    intro current count hvalid hinv
    rw [rawStage_nil]
    exact ⟨le_refl _, Or.inl ⟨current, rfl, hvalid, hinv, fun ordinal draw _ => by
      rw [probedStageScan_nil]⟩⟩
  | cons a xs ih =>
    intro current count hvalid hinv
    obtain ⟨hle, hcases⟩ := return_attribution r o₁ o₂ tape s q w current count hvalid hinv
    rcases hcases with ⟨final, hfinal1, hfinal2, hfinal3, hfinal4⟩
      | ⟨hcapped1, hcapped2⟩ | ⟨ordinal₀, draw₀, d₀, hge₀, hcapord₀, habort1, hfail, hcap⟩
    · have hpair : (countedReturn r o₁ o₂ tape s q w current count).val =
          (some final, (countedReturn r o₁ o₂ tape s q w current count).val.2) :=
        Prod.ext hfinal1 rfl
      rw [rawStage_cons, countedTransition_some, hpair]
      obtain ⟨hle2, hcases2⟩ := ih final _ hfinal2 hfinal3
      refine ⟨by omega, ?_⟩
      rcases hcases2 with ⟨final2, h1, h2, h3, h4⟩ | ⟨hc1, hc2⟩
        | ⟨hc1, ord, draw, d, hge, hcapord, hfail2, hc2⟩
      · refine Or.inl ⟨final2, h1, h2, h3, ?_⟩
        intro ordinal draw hord
        rw [probedStageScan_cons, probedTransition_some, hfinal4 ordinal draw
          (by omega), hpair]
        exact h4 ordinal draw hord
      · exact Or.inr (Or.inl ⟨hc1, hc2⟩)
      · refine Or.inr (Or.inr ⟨hc1, ord, draw, d, by omega, hcapord, hfail2, ?_⟩)
        rw [probedStageScan_cons, probedTransition_some, hfinal4 ord draw (by omega), hpair]
        exact hc2
    · have hpair : (countedReturn r o₁ o₂ tape s q w current count).val =
          (none, (countedReturn r o₁ o₂ tape s q w current count).val.2) :=
        Prod.ext hcapped2 rfl
      rw [rawStage_cons, countedTransition_some, hpair, rawStage_done]
      exact ⟨by omega, Or.inr (Or.inl ⟨rfl, hcapped1⟩)⟩
    · have hpair : (countedReturn r o₁ o₂ tape s q w current count).val =
          (none, (countedReturn r o₁ o₂ tape s q w current count).val.2) :=
        Prod.ext habort1 rfl
      rw [rawStage_cons, countedTransition_some, hpair, rawStage_done]
      refine ⟨by omega, Or.inr (Or.inr ⟨rfl, ordinal₀, draw₀, d₀, by omega, hcapord₀, hfail,
        ?_⟩)⟩
      rw [probedStageScan_cons, probedTransition_some,
        show (probedReturn r o₁ o₂ tape s q w ordinal₀ draw₀ current count none).val =
          ((probedReturn r o₁ o₂ tape s q w ordinal₀ draw₀ current count none).val.1,
            some d₀) from Prod.ext rfl hcap]
      exact probedStageScan_observed_sticky r o₁ o₂ tape s q w ordinal₀ draw₀ xs _ d₀

/-- INTERNAL: `countedStage`'s public value in terms of `rawStage`, at the
stored stage parameters it actually computes from `index` and `tables`. -/
theorem countedStage_eq (tables : LearnedWeights n) (index : ℕ)
    (acc : Option (RestartCursor n) × ℕ) :
    (countedStage r o₁ o₂ tape s tables index acc).val =
      rawStage r o₁ o₂ tape s (ratPower s.ρ (index + 1)).val
        (learnedWeightRead tables (index + 1) s.L).val (List.range s.τ) acc := by
  unfold countedStage rawStage
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]

/-- INTERNAL: `probedStage`'s public value in terms of `probedStageScan`, at
the stored stage parameters it actually computes from `index` and
`tables`. -/
theorem probedStage_eq (tables : LearnedWeights n) (ordinal : ℕ) (draw : Fin 3)
    (index : ℕ) (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    (probedStage r o₁ o₂ tape s tables ordinal draw index acc).val =
      probedStageScan r o₁ o₂ tape s (ratPower s.ρ (index + 1)).val
        (learnedWeightRead tables (index + 1) s.L).val ordinal draw (List.range s.τ) acc := by
  unfold probedStage probedStageScan
  simp only [Arlib.Computation.Charged.val_bind, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]

/-- One stored-parameter stage either reaches a non-invalid continuing
state, exhausts the shared restart cap, or aborts at a draw whose
descriptor is captured by the concrete sticky probe at the matching
ordinal. A probe at or beyond the stage's final count is never disturbed
by this stage's own processing.
PAPER: main.tex:1163-1176,1392-1421 -/
theorem stage_attribution (tables : LearnedWeights n) (index : ℕ) (current : RestartCursor n)
    (count : ℕ) (hvalid : (classifyState current.state).val ≠ .invalid)
    (hinv : current.attempts = count) :
    count ≤ (countedStage r o₁ o₂ tape s tables index (some current, count)).val.2 ∧
    ((∃ final : RestartCursor n,
        (countedStage r o₁ o₂ tape s tables index (some current, count)).val.1 = some final ∧
        (classifyState final.state).val ≠ .invalid ∧
        final.attempts = (countedStage r o₁ o₂ tape s tables index (some current, count)).val.2
        ∧ ∀ ordinal (draw : Fin 3),
          (countedStage r o₁ o₂ tape s tables index (some current, count)).val.2 ≤ ordinal →
          (probedStage r o₁ o₂ tape s tables ordinal draw index ((some current, count), none)).val =
            ((countedStage r o₁ o₂ tape s tables index (some current, count)).val, none))
      ∨ ((countedStage r o₁ o₂ tape s tables index (some current, count)).val.1 = none ∧
          s.restartCap ≤ (countedStage r o₁ o₂ tape s tables index (some current, count)).val.2)
      ∨ ((countedStage r o₁ o₂ tape s tables index (some current, count)).val.1 = none ∧
          ∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧
          ordinal < s.restartCap ∧
          (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
          (probedStage r o₁ o₂ tape s tables ordinal draw index
            ((some current, count), none)).val.2 = some d)) := by
  rw [countedStage_eq]
  simp only [probedStage_eq]
  exact stageScan_attr r o₁ o₂ tape s (ratPower s.ρ (index + 1)).val
    (learnedWeightRead tables (index + 1) s.L).val (List.range s.τ) current count hvalid hinv

end CountingMatroid.Analysis.RestartStageAbortAttribution
