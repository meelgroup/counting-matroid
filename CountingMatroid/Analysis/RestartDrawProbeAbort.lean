import CountingMatroid.Analysis.RestartDrawProbe
import CountingMatroid.Analysis.ChainDrawAbortAttribution
import CountingMatroid.Analysis.RestartStageAbortAttribution
import CountingMatroid.Analysis.ConditionalVarianceTree
import CountingMatroid.Analysis.InitialRestartLaw

set_option autoImplicit false

/-!
Deterministic failure attribution for concrete ordinal probes. Neither tape
coverage nor stopping-prefix replay enters this operational loop invariant.
The restart-level fold repeats the stage-level pattern from
`RestartStageAbortAttribution` one level up, using `stage_attribution` as
the per-index leaf fact: each stored-parameter stage either continues,
exhausts the shared restart cap, or aborts at a concretely captured draw.
-/
namespace CountingMatroid.Analysis.RestartDrawProbeAbort
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RestartAttemptAccounting
open CountingMatroid.Analysis.RestartDrawProbe
open CountingMatroid.Analysis.RestartStageAbortAttribution

variable {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
  (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)

/-- INTERNAL: The raw (uninstrumented) restart scan over an arbitrary list
and starting accumulator. -/
noncomputable def rawRestartScan (xs : List ℕ) (acc : Option (RestartCursor n) × ℕ) :
    Option (RestartCursor n) × ℕ :=
  (Arlib.Computation.Charged.foldl
    (fun acc index => countedStage r o₁ o₂ tape s tables index acc) xs acc).val

/-- INTERNAL: The probed restart scan over an arbitrary list, at a fixed
ordinal and draw index, and starting accumulator. -/
noncomputable def probedRestartScan (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ) :=
  (Arlib.Computation.Charged.foldl
    (fun acc index => probedStage r o₁ o₂ tape s tables ordinal draw index acc) xs acc).val

theorem rawRestartScan_nil (acc : Option (RestartCursor n) × ℕ) :
    rawRestartScan r o₁ o₂ tape s tables [] acc = acc := rfl

theorem probedRestartScan_nil (ordinal : ℕ) (draw : Fin 3)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedRestartScan r o₁ o₂ tape s tables ordinal draw [] acc = acc := rfl

theorem rawRestartScan_cons (a : ℕ) (xs : List ℕ) (acc : Option (RestartCursor n) × ℕ) :
    rawRestartScan r o₁ o₂ tape s tables (a :: xs) acc =
      rawRestartScan r o₁ o₂ tape s tables xs
        (countedStage r o₁ o₂ tape s tables a acc).val := by
  unfold rawRestartScan
  rw [Arlib.Computation.Charged.val_foldl_cons]

theorem probedRestartScan_cons (ordinal : ℕ) (draw : Fin 3) (a : ℕ) (xs : List ℕ)
    (acc : (Option (RestartCursor n) × ℕ) × Option (ℕ × ℕ)) :
    probedRestartScan r o₁ o₂ tape s tables ordinal draw (a :: xs) acc =
      probedRestartScan r o₁ o₂ tape s tables ordinal draw xs
        (probedStage r o₁ o₂ tape s tables ordinal draw a acc).val := by
  unfold probedRestartScan
  rw [Arlib.Computation.Charged.val_foldl_cons]

/-- INTERNAL: Once aborted, no further elements of the list change the raw
accumulator. -/
theorem rawRestartScan_done (xs : List ℕ) (cnt : ℕ) :
    rawRestartScan r o₁ o₂ tape s tables xs (none, cnt) = (none, cnt) := by
  induction xs with
  | nil => rw [rawRestartScan_nil]
  | cons a xs ih =>
    rw [rawRestartScan_cons, countedStage_eq, rawStage_done]
    exact ih

/-- INTERNAL: Once aborted, no further elements of the list change the
probed accumulator, whatever ordinal, draw, or observation. -/
theorem probedRestartScan_done (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ) (cnt : ℕ)
    (observed : Option (ℕ × ℕ)) :
    probedRestartScan r o₁ o₂ tape s tables ordinal draw xs ((none, cnt), observed) =
      ((none, cnt), observed) := by
  induction xs with
  | nil => rw [probedRestartScan_nil]
  | cons a xs ih =>
    rw [probedRestartScan_cons, probedStage_eq, probedStageScan_done]
    exact ih

/-- INTERNAL: An already captured observation survives the whole remaining
restart, whatever its underlying raw state. -/
theorem probedRestartScan_observed_sticky (ordinal : ℕ) (draw : Fin 3) (xs : List ℕ)
    (acc : Option (RestartCursor n) × ℕ) (d : ℕ × ℕ) :
    (probedRestartScan r o₁ o₂ tape s tables ordinal draw xs (acc, some d)).2 = some d := by
  induction xs generalizing acc with
  | nil => rw [probedRestartScan_nil]
  | cons a xs ih =>
    rw [probedRestartScan_cons, probedStage_eq,
      show (probedStageScan r o₁ o₂ tape s (ratPower s.ρ (a + 1)).val
            (Model.Operations.learnedWeightRead tables (a + 1) s.L).val ordinal draw
            (List.range s.τ) (acc, some d)) =
          ((probedStageScan r o₁ o₂ tape s (ratPower s.ρ (a + 1)).val
            (Model.Operations.learnedWeightRead tables (a + 1) s.L).val ordinal draw
            (List.range s.τ) (acc, some d)).1, some d) from
        Prod.ext rfl (probedStageScan_observed_sticky r o₁ o₂ tape s
          (ratPower s.ρ (a + 1)).val
          (Model.Operations.learnedWeightRead tables (a + 1) s.L).val ordinal draw
          (List.range s.τ) acc d)]
    exact ih _

/-- INTERNAL: Positivity/attribution target for one restart scan, generalized
over an arbitrary remaining list and starting accumulator. -/
theorem restartScan_attr :
    ∀ (xs : List ℕ) (current : RestartCursor n) (count : ℕ),
      (classifyState current.state).val ≠ .invalid → current.attempts = count →
      count ≤ (rawRestartScan r o₁ o₂ tape s tables xs (some current, count)).2 ∧
      ((∃ final : RestartCursor n,
          (rawRestartScan r o₁ o₂ tape s tables xs (some current, count)).1 = some final ∧
          (classifyState final.state).val ≠ .invalid ∧
          final.attempts = (rawRestartScan r o₁ o₂ tape s tables xs (some current, count)).2)
        ∨ ((rawRestartScan r o₁ o₂ tape s tables xs (some current, count)).1 = none ∧
            s.restartCap ≤ (rawRestartScan r o₁ o₂ tape s tables xs (some current, count)).2)
        ∨ ((rawRestartScan r o₁ o₂ tape s tables xs (some current, count)).1 = none ∧
            ∃ (ordinal : ℕ) (draw : Fin 3) (d : ℕ × ℕ), count ≤ ordinal ∧
              ordinal < s.restartCap ∧
              (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none ∧
              (probedRestartScan r o₁ o₂ tape s tables ordinal draw xs
                ((some current, count), none)).2 = some d)) := by
  intro xs
  induction xs with
  | nil =>
    intro current count hvalid hinv
    rw [rawRestartScan_nil]
    exact ⟨le_refl _, Or.inl ⟨current, rfl, hvalid, hinv⟩⟩
  | cons a xs ih =>
    intro current count hvalid hinv
    obtain ⟨hle, hcases⟩ := stage_attribution r o₁ o₂ tape s tables a current count hvalid hinv
    rcases hcases with ⟨final, hfinal1, hfinal2, hfinal3, hfinal4⟩
      | ⟨hcapped1, hcapped2⟩
      | ⟨habort1, ordinal₀, draw₀, d₀, hge₀, hcapord₀, hfail, hcap⟩
    · have hpair : (countedStage r o₁ o₂ tape s tables a (some current, count)).val =
          (some final, (countedStage r o₁ o₂ tape s tables a (some current, count)).val.2) :=
        Prod.ext hfinal1 rfl
      rw [rawRestartScan_cons, hpair]
      obtain ⟨hle2, hcases2⟩ := ih final _ hfinal2 hfinal3
      refine ⟨by omega, ?_⟩
      rcases hcases2 with ⟨final2, h1, h2, h3⟩ | ⟨hc1, hc2⟩
        | ⟨hc1, ord, draw, d, hge, hcapord, hfail2, hc2⟩
      · exact Or.inl ⟨final2, h1, h2, h3⟩
      · exact Or.inr (Or.inl ⟨hc1, hc2⟩)
      · refine Or.inr (Or.inr ⟨hc1, ord, draw, d, by omega, hcapord, hfail2, ?_⟩)
        rw [probedRestartScan_cons, hfinal4 ord draw (by omega), hpair]
        exact hc2
    · have hpair : (countedStage r o₁ o₂ tape s tables a (some current, count)).val =
          (none, (countedStage r o₁ o₂ tape s tables a (some current, count)).val.2) :=
        Prod.ext hcapped1 rfl
      rw [rawRestartScan_cons, hpair, rawRestartScan_done]
      exact ⟨by omega, Or.inr (Or.inl ⟨rfl, hcapped2⟩)⟩
    · have hpair : (countedStage r o₁ o₂ tape s tables a (some current, count)).val =
          (none, (countedStage r o₁ o₂ tape s tables a (some current, count)).val.2) :=
        Prod.ext habort1 rfl
      rw [rawRestartScan_cons, hpair, rawRestartScan_done]
      refine ⟨by omega, Or.inr (Or.inr ⟨rfl, ordinal₀, draw₀, d₀, by omega, hcapord₀, hfail,
        ?_⟩)⟩
      rw [probedRestartScan_cons,
        show (probedStage r o₁ o₂ tape s tables ordinal₀ draw₀ a
              ((some current, count), none)).val =
            ((probedStage r o₁ o₂ tape s tables ordinal₀ draw₀ a
              ((some current, count), none)).val.1, some d₀) from
          Prod.ext rfl hcap]
      exact probedRestartScan_observed_sticky r o₁ o₂ tape s tables ordinal₀ draw₀ xs _ d₀

/-- INTERNAL: The non-invalid, non-initial first transversal is always a
valid live start for the restart scan. -/
private theorem fresh_valid (tape : ℕ → Bool) (cursor : ℕ) :
    (classifyState (freshTransversal n tape cursor).val.1).val ≠ .invalid := by
  rw [InitialRestartLaw.freshTransversal_value]
  have heq : Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))) =
      CountingMatroid.Analysis.TransversalPartition.transversalState
        (Finset.univ.filter (fun i : Fin n => tape (cursor + i) = false)) := by
    unfold CountingMatroid.Analysis.TransversalPartition.transversalState
    congr 1
    funext i
    simp
  rw [heq, CountingMatroid.Analysis.ConditionalVarianceTree.transversal_state_classified]
  intro h; cases h

/-- A restart abort below the shared attempt cap is witnessed by an actual
failed draw at its concrete ordinal probe. This is independent of schedule
arithmetic and of the earlier phase history.
PAPER: main.tex:1163-1176,1392-1421 -/
theorem restart_draw_probe_abort {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) (hn : 0 < n)
    (habort : (countedRestart r o₁ o₂ tape s tables j cursor).val.1 = none) :
    s.restartCap ≤ (countedRestart r o₁ o₂ tape s tables j cursor).val.2 ∨
      ∃ (k : Fin (3 * s.restartCap)) (d : ℕ × ℕ),
        restartDrawProbe r o₁ o₂ tape s tables j cursor k = some d ∧
        (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none := by
  set initial := (freshTransversal n tape cursor).val with hinitial
  have hraweq : (countedRestart r o₁ o₂ tape s tables j cursor).val =
      ((rawRestartScan r o₁ o₂ tape s tables (List.range j)
        (some ⟨initial.1, initial.2, 0⟩, 0)).1.map
          (fun current => (current.state, current.bitCursor)),
        (rawRestartScan r o₁ o₂ tape s tables (List.range j)
          (some ⟨initial.1, initial.2, 0⟩, 0)).2) := by
    unfold countedRestart rawRestartScan
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
      Arlib.Computation.Charged.repeatFor, hinitial]
  have hvalid0 : (classifyState (⟨initial.1, initial.2, 0⟩ : RestartCursor n).state).val ≠
      .invalid := fresh_valid tape cursor
  obtain ⟨hle, hcases⟩ := restartScan_attr r o₁ o₂ tape s tables (List.range j)
    ⟨initial.1, initial.2, 0⟩ 0 hvalid0 rfl
  have habort' : (rawRestartScan r o₁ o₂ tape s tables (List.range j)
      (some ⟨initial.1, initial.2, 0⟩, 0)).1 = none := by
    have := habort
    rw [hraweq] at this
    simpa only [Option.map_eq_none_iff] using this
  rcases hcases with ⟨final, hfinal1, _, _⟩ | ⟨hcapped1, hcapped2⟩
    | ⟨habort1, ordinal, draw, d, hge, hcapord, hfail, hcap⟩
  · exact absurd hfinal1 (by rw [habort']; simp)
  · exact Or.inl (by rw [hraweq]; simpa using hcapped2)
  · right
    have hk : (3 : ℕ) * ordinal + draw.val < 3 * s.restartCap := by
      have := draw.isLt
      omega
    refine ⟨⟨3 * ordinal + draw.val, hk⟩, d, ?_, hfail⟩
    unfold restartDrawProbe probedRestart
    have hidx1 : (3 * ordinal + draw.val) / 3 = ordinal := by omega
    have hidx2 : (3 * ordinal + draw.val) % 3 = draw.val := by omega
    simp only [hidx1, hidx2]
    simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
      Arlib.Computation.Charged.repeatFor, hinitial]
    change (probedRestartScan r o₁ o₂ tape s tables ordinal draw (List.range j)
      ((some ⟨initial.1, initial.2, 0⟩, 0), none)).2 = some d
    exact hcap

end CountingMatroid.Analysis.RestartDrawProbeAbort

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · restart-level fold (`restartScan_attr`) repeats the
  stage-level attribution pattern one level up using `stage_attribution` as
  the per-index leaf fact, closing `restart_draw_probe_abort`.
-/
