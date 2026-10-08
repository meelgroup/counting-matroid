import CountingMatroid.Analysis.PhaseObservationExperiment
import CountingMatroid.Analysis.ObservationRoundDrawCover

set_option autoImplicit false

/-!
The deterministic observation-loop failure characterization and the finite
union-bound reduction are proved below. The quantitative theorem uses two
separate open child obligations: the covered finite-suffix rejection law and
the operational construction of three draw-site prefix families. The
generic transfer to adaptive denominators is proved in the sampling child.
The original theorem statement and its zero-padded tape are unchanged.
-/

namespace CountingMatroid.Analysis.ConditionalObservationAbortMass

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.PhaseObservationExperiment

/-- INTERNAL: Evaluate a bounded charged loop after appending its last round. -/
theorem repeatFor_value_succ {α : Type}
    (f : ℕ → α → Arlib.Computation.Charged Model.Operations.Op
      Model.Operations.Cell α) (k : ℕ) (initial : α) :
    (Arlib.Computation.Charged.repeatFor f (k + 1) initial).val =
      (f k (Arlib.Computation.Charged.repeatFor f k initial).val).val := by
  have happend (xs ys : List ℕ) (b : α) :
      (Arlib.Computation.Charged.foldl (fun b i => f i b) (xs ++ ys) b).val =
        (Arlib.Computation.Charged.foldl (fun b i => f i b) ys
          (Arlib.Computation.Charged.foldl (fun b i => f i b) xs b).val).val := by
    induction xs generalizing b with
    | nil => rfl
    | cons x xs ih =>
        simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
          using ih (f x b).val
  unfold Arlib.Computation.Charged.repeatFor
  rw [List.range_succ, happend]
  rfl

/-- INTERNAL: An absorbing option loop aborts exactly when one reached round
first returns none. The witness uses the actual prefix of the same loop.
TEXLINE: main.tex:1177-1187 -/
theorem repeatFor_first_abort {α : Type}
    (f : ℕ → Option α → Arlib.Computation.Charged Model.Operations.Op
      Model.Operations.Cell (Option α))
    (hnone : ∀ k, (f k none).val = none) (N : ℕ) (initial : α) :
    (Arlib.Computation.Charged.repeatFor f N (some initial)).val = none ↔
      ∃ k < N, ∃ current,
        (Arlib.Computation.Charged.repeatFor f k (some initial)).val = some current ∧
        (f k (some current)).val = none := by
  induction N with
  | zero => simp [Arlib.Computation.Charged.repeatFor]
  | succ N ih =>
      rw [repeatFor_value_succ]
      cases hprefix : (Arlib.Computation.Charged.repeatFor f N (some initial)).val with
      | none =>
          rw [hnone]
          constructor
          · intro _
            obtain ⟨k, hk, current, hc, hf⟩ := ih.mp hprefix
            exact ⟨k, Nat.lt_succ_of_lt hk, current, hc, hf⟩
          · intro _; rfl
      | some current =>
          constructor
          · intro hf
            exact ⟨N, Nat.lt_succ_self N, current, hprefix, hf⟩
          · rintro ⟨k, hk, reached, hr, hf⟩
            have hkle : k ≤ N := Nat.le_of_lt_succ hk
            rcases hkle.eq_or_lt with heq | hlt
            · subst k
              have heq : current = reached := Option.some.inj (hprefix.symm.trans hr)
              subst reached
              exact hf
            · have habort := ih.mpr ⟨k, hlt, reached, hr, hf⟩
              rw [hprefix] at habort
              contradiction

/-- INTERNAL: Name one iteration of the actual observation loop, including
its absorbing abort and initial-state recording branches.
TEXLINE: main.tex:1177-1187 -/
def observationStep {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (index : ℕ) (current : Option (ObservationCursor n)) :
    Arlib.Computation.Charged Model.Operations.Op Model.Operations.Cell
      (Option (ObservationCursor n)) := do
  match current with
  | none => pure none
  | some current =>
      let onStart ← Model.Operations.natEqual index 0
      if onStart then recordObservation r o₁ o₂ s.ρ current
      else
        let next ← chainStep r o₁ o₂ tape s.drawTrials q w
          current.state current.bitCursor
        match next with
        | none => pure none
        | some (state, bitCursor) =>
            recordObservation r o₁ o₂ s.ρ
              ⟨state, bitCursor, current.counts, current.numeratorSum⟩

/-- INTERNAL: Truncating the actual observation loop changes only its loop
bound. Stating this for an arbitrary schedule avoids reducing the entire
charged setup computation when using a concrete setup schedule.
TEXLINE: main.tex:1177-1187 -/
theorem observePhase_prefix_value {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (w : Multipliers n) (k : ℕ) (start : PairedSet n × ℕ) :
    (observePhase r o₁ o₂ tape {s with observations := k} q w start).val =
      (Arlib.Computation.Charged.repeatFor (observationStep r o₁ o₂ tape s q w) k
        (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val := by
  rfl

/-- INTERNAL: Recording aborts exactly at an invalid classifier output;
zero empirical type frequencies are checked later by finishPhase.
TEXLINE: main.tex:1177-1187 -/
theorem recordObservation_none_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current : ObservationCursor n) :
    (recordObservation r o₁ o₂ rho current).val = none ↔
      (classifyState current.state).val = .invalid := by
  cases hkind : (classifyState current.state).val <;>
    simp only [recordObservation, Arlib.Computation.Charged.val_bind, hkind,
      Arlib.Computation.Charged.val_pure, Option.some_ne_none, reduceCtorEq]

/-- INTERNAL: One observation iteration fails through either its classifier
check or its chain transition, with the transition's actual output retained.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem observationStep_none_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (w : Multipliers n) (k : ℕ) (current : ObservationCursor n) :
    (observationStep r o₁ o₂ tape s q w k (some current)).val = none ↔
      if k = 0 then (classifyState current.state).val = .invalid
      else (chainStep r o₁ o₂ tape s.drawTrials q w
          current.state current.bitCursor).val = none ∨
        ∃ next : PairedSet n × ℕ,
          (chainStep r o₁ o₂ tape s.drawTrials q w
            current.state current.bitCursor).val = some next ∧
          (classifyState next.1).val = .invalid := by
  by_cases hk : k = 0
  · simp only [observationStep, Arlib.Computation.Charged.val_bind,
      Model.Operations.natEqual, Arlib.Computation.Charged.val_op,
      hk, beq_self_eq_true, ite_true]
    exact recordObservation_none_iff r o₁ o₂ s.ρ current
  · simp only [observationStep, Arlib.Computation.Charged.val_bind,
      Model.Operations.natEqual, Arlib.Computation.Charged.val_op,
      beq_eq_false_iff_ne.mpr hk, Bool.false_eq_true, if_neg hk, ite_false]
    cases hnext : (chainStep r o₁ o₂ tape s.drawTrials q w
        current.state current.bitCursor).val with
    | none => simp only [Arlib.Computation.Charged.val_pure, true_or]
    | some next =>
        cases next with
        | mk state cursor =>
          rw [recordObservation_none_iff]
          simp only [reduceCtorEq, false_or, Option.some.injEq,
            exists_eq_left']

/-- INTERNAL: A concrete observation abort has a first failing iteration,
reached by the actual correlated trajectory on the same tape.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem observePhase_abort_iff {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (q : ℚ) (w : Multipliers n) (start : PairedSet n × ℕ) :
    (observePhase r o₁ o₂ tape s q w start).val = none ↔
      ∃ k < s.observations, ∃ current : ObservationCursor n,
        (Arlib.Computation.Charged.repeatFor (observationStep r o₁ o₂ tape s q w) k
          (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val =
            some current ∧
        (observationStep r o₁ o₂ tape s q w k (some current)).val = none := by
  change (Arlib.Computation.Charged.repeatFor (observationStep r o₁ o₂ tape s q w)
    s.observations
    (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val = none ↔ _
  exact repeatFor_first_abort _ (fun _ => rfl) _ _

/-- INTERNAL: Conditional finite-suffix mass of an actual observation abort
after a successful restart. Only capped draws may abort a valid trajectory;
at most three such draws occur per observation transition.
TEXLINE: main.tex:1177-1187,1392-1421 -/
theorem conditional_observation_abort_mass (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hn : 0 < n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (hpositive : 0 < commonBaseCount M₁ M₂)
    (j : ℕ) (hj : j < (CountingMatroid.Interface.Pseudocode.setup n p).L)
    (pref : List Bool) (hprefix : SuccessfulPhasePrefix n r o₁ o₂ p j pref) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        ∃ start,
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = some start ∧
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s (s.ρ ^ j) current.currentWeights start).val = none} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal ((3 * (s.observations : ℚ) *
          (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
  classical
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let t := CountingMatroid.Model.Run.blockLength n r p - pref.length
  let E : Fin s.observations → Set (List Bool) := fun k =>
    {suffix | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        ∃ start,
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = some start ∧
          ∃ reached : ObservationCursor n,
            (Arlib.Computation.Charged.repeatFor
              (observationStep r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
                s (s.ρ ^ j) current.currentWeights) k.val
              (some ⟨start.1, start.2, (Model.Operations.allocateCounts n).val, 0⟩)).val =
                some reached ∧
            (observationStep r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
              s (s.ρ ^ j) current.currentWeights k.val (some reached)).val = none}
  have hevent : {suffix : List Bool | suffix.length = t ∧
      (∀ a < j, FirstPhaseFailure.CertifiedPhase r o₁ o₂
        (fun i => ((pref ++ suffix)[i]?).getD false) s a) ∧
      ∃ current : AnnealingCursor n,
        BoundedRunPhaseHistory.phaseHistory r o₁ o₂
          (fun i => ((pref ++ suffix)[i]?).getD false) s j = some current ∧
        ∃ start,
          (restartPhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s current.tables j current.bitCursor).val = some start ∧
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            s (s.ρ ^ j) current.currentWeights start).val = none} = ⋃ k, E k := by
    ext suffix
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, E, observePhase_abort_iff]
    constructor
    · rintro ⟨hlen, hprev, current, hh, start, hs, k, hk, reached, hrch, hb⟩
      exact ⟨⟨k, hk⟩, hlen, hprev, current, hh, start, hs, reached, hrch, hb⟩
    · rintro ⟨k, hlen, hprev, current, hh, start, hs, reached, hrch, hb⟩
      exact ⟨hlen, hprev, current, hh, start, hs, k.val, k.isLt, reached, hrch, hb⟩
  have hround (k : Fin s.observations) :
      (Set.ncard (E k) : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        ENNReal.ofReal ((3 * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
    obtain ⟨covers, hcover⟩ := ObservationRoundDrawCover.observation_round_draw_cover
      n r M₁ M₂ o₁ o₂ p hn hfull hr h₁ h₂ hpositive j hj pref hprefix k.val k.isLt
    let D : Fin 3 → Set (List Bool) := fun site =>
      {suffix | suffix.length = t ∧
        ∃ head ∈ (covers site).prefixes, head <+: suffix ∧
          (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
            s.drawTrials ((covers site).denominator head)
            (pref.length + head.length)).val.1 = none}
    have hsubset : E k ⊆ ⋃ site, D site := by
      rintro suffix ⟨hlen, hprev, current, hh, start, hs, reached, hrch, hfail⟩
      have hshort :
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            {s with observations := k.val} (s.ρ ^ j)
            current.currentWeights start).val = some reached := by
        rw [observePhase_prefix_value]
        exact hrch
      have hlong :
          (observePhase r o₁ o₂ (fun i => ((pref ++ suffix)[i]?).getD false)
            {s with observations := k.val + 1} (s.ρ ^ j)
            current.currentWeights start).val = none := by
        rw [observePhase_prefix_value, repeatFor_value_succ, hrch]
        exact hfail
      obtain ⟨site, head, hhead, hpref, hdraw⟩ := hcover suffix hlen
        ⟨hprev, current, hh, start, hs, reached, hshort, hlong⟩
      exact Set.mem_iUnion.mpr ⟨site, hlen, head, hhead, hpref, hdraw⟩
    have hfinite : (⋃ site, D site).Finite :=
      (List.finite_length_eq Bool t).subset (by
        intro suffix hsuffix
        obtain ⟨site, hsite⟩ := Set.mem_iUnion.mp hsuffix
        exact hsite.1)
    have hcount : Set.ncard (E k) ≤ ∑ site, Set.ncard (D site) :=
      (Set.ncard_le_ncard hsubset hfinite).trans (Set.ncard_iUnion_le_of_fintype D)
    calc
      _ ≤ ∑ site, (Set.ncard (D site) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
        rw [← Finset.sum_mul, ← Nat.cast_sum]
        exact mul_le_mul_left (Nat.cast_le.mpr hcount) _
      _ ≤ ∑ _site : Fin 3,
          ENNReal.ofReal (((1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
        apply Finset.sum_le_sum
        intro site _
        exact FiniteSuffixDrawAbortMass.adaptive_draw_abort_mass pref s.drawTrials t
          (covers site)
      _ = ENNReal.ofReal ((3 * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
        congr 1
        push_cast
        ring
  change (Set.ncard _ : ENNReal) * (1 / 2 : ENNReal) ^ t ≤ _
  rw [hevent]
  calc
    (Set.ncard (⋃ k, E k) : ENNReal) * (1 / 2 : ENNReal) ^ t ≤
        ∑ k, (Set.ncard (E k) : ENNReal) * (1 / 2 : ENNReal) ^ t := by
      rw [← Finset.sum_mul, ← Nat.cast_sum]
      exact mul_le_mul_left (Nat.cast_le.mpr (Set.ncard_iUnion_le_of_fintype E)) _
    _ ≤ ∑ _k : Fin s.observations,
        ENNReal.ofReal ((3 * (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) :=
      Finset.sum_le_sum (fun k _ => hround k)
    _ = ENNReal.ofReal ((3 * (s.observations : ℚ) *
        (1 / 2 : ℚ) ^ s.drawTrials : ℚ) : ℝ) := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      congr 1
      push_cast
      ring

end CountingMatroid.Analysis.ConditionalObservationAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · decomposed · reduced each reached-round estimate to a covered finite-suffix rejection law and an operational three-draw prefix-cover construction; the adaptive prefix-cylinder transfer is proved.

* r25 · reduced · proved first reached observation-failure witnesses and exact recording/iteration abort characterizations; the original mass bound reduces by a finite union bound to one adaptive reached-round capped-draw estimate, still open inside the parent.

* r24 · attempted · unfolded the actual observation loop; the capped-draw law must exclude invalid states and account for adaptive finite-block coverage after the restart.
-/
