import CountingMatroid.Analysis.RecordedObservationTrajectory
import CountingMatroid.Analysis.ChainStepNoninvalid
import CountingMatroid.Analysis.FiniteStoppedFiberMass

set_option autoImplicit false

/-! Covered finite-tape bounds for the transition part of recorded observations. -/
namespace CountingMatroid.Analysis.RecordedTraceContinuationBound
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.RecordedObservationTrajectory
open CountingMatroid.Analysis.FiniteStoppedFiberMass

/-- INTERNAL: Classifier-valid states have the n-element cardinality needed
by the one-step subkernel hypothesis. -/
theorem classified_card {n : ℕ} (state : PairedSet n)
    (hv : (classifyState state).val ≠ .invalid) : state.card = n := by
  classical
  cases hk : (classifyState state).val with
  | invalid => exact False.elim (hv hk)
  | transversal =>
    have hex : ∃ A : Finset (Fin n), TransversalPartition.transversalState A = state := by
      by_contra hn
      have hnone : ∀ A : Finset (Fin n), TransversalPartition.transversalState A ≠ state :=
        by simpa only [not_exists] using hn
      have h := ConditionalVarianceTree.transversal_sum_reindex
        (fun x : PairedSet n => if x = state then (1 : ℝ) else 0)
      have hleft : (∑ x : PairedSet n, if (classifyState x).val = .transversal then
          (if x = state then (1 : ℝ) else 0) else 0) = 1 := by
        rw [Finset.sum_eq_single state]
        · simp [hk]
        · intro x _ hx
          simp [hx]
        · simp
      rw [hleft] at h
      simp only [hnone, if_false, Finset.sum_const_zero] at h
      exact one_ne_zero h
    obtain ⟨A, rfl⟩ := hex
    unfold TransversalPartition.transversalState
    rw [Finset.card_image_of_injective]
    · simp
    · intro a b h
      exact congrArg Prod.fst h
  | defect i j =>
    have hij : i ≠ j := by
      intro heq
      subst j
      unfold classifyState at hk
      simp only [Arlib.Computation.Charged.val_bind] at hk
      split at hk
      · cases hk
      · split at hk
        · cases hk
        · simp only [Arlib.Computation.Charged.val_bind] at hk
          rename_i a b _ _
          by_cases hequal : (Model.Operations.indexEqual a b).val = true
          · rw [if_pos hequal] at hk
            cases hk
          · rw [if_neg hequal] at hk
            have heq := StateKind.defect.inj hk
            have hab : a = b := heq.1.trans heq.2.symm
            apply hequal
            simp [Model.Operations.indexEqual, hab]
        · cases hk
    exact OmittedRankWeightPolynomial.defect_card state ⟨i,j,hij⟩ hk

/-- INTERNAL: Recording changes neither the current state nor its bit cursor. -/
theorem record_preserves {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (rho : ℚ) (current next : ObservationCursor n)
    (h : (recordObservation r o₁ o₂ rho current).val = some next) :
    next.state = current.state ∧ next.bitCursor = current.bitCursor := by
  unfold recordObservation at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · cases h
  · simp only [Arlib.Computation.Charged.val_bind] at h
    cases (Option.some.inj h).symm
    exact ⟨rfl, rfl⟩
  · simp only [Arlib.Computation.Charged.val_bind] at h
    cases (Option.some.inj h).symm
    exact ⟨rfl, rfl⟩

/-- INTERNAL: A successful observation attempt replays its consumed interval. -/
theorem attempt_success_interval {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (current : ObservationCursor n) (k : ℕ) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => (observationAttempt r o₁ o₂ tape s q weights k (some current)).val)
      ObservationCursor.bitCursor current.bitCursor := by
  intro tape next hrun
  unfold observationAttempt at hrun ⊢
  simp only [Arlib.Computation.Charged.val_bind] at hrun ⊢
  by_cases hstart : (Model.Operations.natEqual k 0).val = true
  · rw [if_pos hstart] at hrun
    simp only [if_pos hstart]
    have hp := record_preserves r o₁ o₂ s.ρ current next hrun
    exact ⟨hp.2.symm.le, fun _ _ => hrun⟩
  · rw [if_neg hstart] at hrun
    simp only [if_neg hstart]
    simp only [Arlib.Computation.Charged.val_bind] at hrun ⊢
    cases hchain : (chainStep r o₁ o₂ tape s.drawTrials q weights
        current.state current.bitCursor).val with
    | none => simp [hchain] at hrun
    | some step =>
      simp only [hchain] at hrun
      have hp := record_preserves r o₁ o₂ s.ρ
        ⟨step.1,step.2,current.counts,current.numeratorSum⟩ next hrun
      have hi := ChainStepIntervalReplay.chainStep_success_interval r o₁ o₂
        s.drawTrials q weights current.state current.bitCursor tape step hchain
      refine ⟨hi.1.trans hp.2.symm.le, ?_⟩
      intro other hagree
      have hreplay := hi.2 other (by simpa only [hp.2] using hagree)
      dsimp only at hreplay
      rw [hreplay]
      cases step
      exact hrun

/-- INTERNAL: Product of the ideal transitions to a specified sequence of destinations. -/
noncomputable def continuationWeight {α : Type} [Fintype α]
    (P : Arlib.MarkovChains.FinChain α) : α → List α → ℝ
  | _, [] => 1
  | current, next :: rest => P current next * continuationWeight P next rest

/-- INTERNAL: Every specified continuation has nonnegative ideal weight. -/
theorem continuationWeight_nonneg {α : Type} [Fintype α]
    (P : Arlib.MarkovChains.FinChain α) (current : α) (states : List α) :
    0 ≤ continuationWeight P current states := by
  induction states generalizing current with
  | nil => exact zero_le_one
  | cons a states ih => exact mul_nonneg (P.coe_nonneg _ _) (ih a)

/-- INTERNAL: Covered successful transition observations are dominated by the
product of their one-step subkernel bounds; recording reads no random bits.
TEXLINE: main.tex:1181-1187,1392-1421 -/
theorem trace_continuation_bound {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (P : Arlib.MarkovChains.FinChain (PairedSet n))
    (hstep : ∀ (pref : List Bool) (u : ℕ) (state next : PairedSet n),
      state.card = n → (classifyState state).val ≠ .invalid →
      fairMass pref u (fun tape => ∃ stop, stop ≤ pref.length + u ∧
        (chainStep r o₁ o₂ tape s.drawTrials q weights state pref.length).val =
          some (next, stop)) ≤ P state next)
    (indices : List ℕ) (hpositive : ∀ k ∈ indices, k ≠ 0)
    (states : List (PairedSet n)) (hlen : states.length = indices.length)
    (head : List Bool) (t : ℕ) (current : ObservationCursor n)
    (hcursor : current.bitCursor = head.length)
    (hvalid : (classifyState current.state).val ≠ .invalid) :
    fairMass head t (fun tape => ∃ final : ObservationCursor n,
      final.bitCursor ≤ head.length + t ∧
      recordedObservationTrace r o₁ o₂ tape s q weights indices (some current) =
        some (final, states)) ≤ continuationWeight P current.state states := by
  classical
  induction indices generalizing states head t current with
  | nil =>
    have hs : states = [] := List.length_eq_zero_iff.mp hlen
    subst states
    change _ ≤ 1
    unfold fairMass
    apply le_trans (Finset.sum_le_sum (fun bits _ => ?_))
      (show (∑ _ : List.Vector Bool t, 1 / (2 : ℝ)^t) ≤ 1 by simp [card_vector])
    split_ifs
    · exact le_rfl
    · positivity
  | cons k ks ih =>
    cases states with
    | nil => simp at hlen
    | cons a rest =>
      have hk : k ≠ 0 := hpositive k (by simp)
      have hks : ∀ j ∈ ks, j ≠ 0 := fun j hj => hpositive j (by simp [hj])
      have hrest : rest.length = ks.length := by simpa using hlen
      let f := fun tape => (chainStep r o₁ o₂ tape s.drawTrials q weights
        current.state head.length).val
      let E := fun tape stop => ∃ middle final : ObservationCursor n,
        (recordObservation r o₁ o₂ s.ρ
          ⟨a, stop, current.counts, current.numeratorSum⟩).val = some middle ∧
        final.bitCursor ≤ head.length+t ∧
        recordedObservationTrace r o₁ o₂ tape s q weights ks (some middle) =
          some (final, rest)
      have hevent : ∀ bits : List.Vector Bool t,
        (∃ final : ObservationCursor n, final.bitCursor ≤ head.length+t ∧
          recordedObservationTrace r o₁ o₂ (finiteTape (head ++ bits.val)) s q weights
            (k::ks) (some current) = some (final, a::rest)) →
        ∃ stop, stop ≤ head.length+t ∧ f (finiteTape (head ++ bits.val)) =
          some (a,stop) ∧ E (finiteTape (head ++ bits.val)) stop := by
        intro bits
        rintro ⟨final, hfinal, ht⟩
        let tape := finiteTape (head ++ bits.val)
        change recordedObservationTrace r o₁ o₂ tape s q weights
          (k::ks) (some current) = some (final,a::rest) at ht
        have hattempt : (observationAttempt r o₁ o₂ tape s q weights k
            (some current)).val =
          (f tape).bind (fun step => (recordObservation r o₁ o₂ s.ρ
            ⟨step.1,step.2,current.counts,current.numeratorSum⟩).val) := by
          simp [observationAttempt, Model.Operations.natEqual, hk, f, hcursor,
            Arlib.Computation.Charged.val_bind]
          cases hc : (chainStep r o₁ o₂ tape s.drawTrials q weights
            current.state head.length).val with
          | none => simp
          | some step => cases step; simp
        cases hf : f tape with
        | none =>
          simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
            Option.bind_none, reduceCtorEq] at ht
        | some step =>
          cases hr : (recordObservation r o₁ o₂ s.ρ
            ⟨step.1,step.2,current.counts,current.numeratorSum⟩).val with
          | none =>
            simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
              Option.bind_some, hr, Option.bind_none, reduceCtorEq] at ht
          | some middle =>
            cases htail : recordedObservationTrace r o₁ o₂ tape s q weights ks
                (some middle) with
            | none =>
              simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
                Option.bind_some, hr, htail, Option.bind_none, reduceCtorEq] at ht
            | some result =>
              rcases result with ⟨finished, recorded⟩
              simp +instances only [recordedObservationTrace, Option.bind_eq_bind, hattempt, hf,
                Option.bind_some, hr, htail, Option.pure_def, Option.some.injEq,
                Prod.mk.injEq, List.cons.injEq] at ht
              obtain ⟨hfinish, hstate, hrecorded⟩ := ht
              subst finished
              subst recorded
              have hp := record_preserves r o₁ o₂ s.ρ _ middle hr
              have ha : step.1 = a := hp.1.symm.trans hstate
              have hmono : middle.bitCursor ≤ final.bitCursor := by
                have hproj := recorded_trace_projection r o₁ o₂ tape s q weights ks
                  (some middle)
                rw [htail] at hproj
                have hreplay := ChainStepIntervalReplay.foldl_successReplay
                  (fun tape acc k => observationAttempt r o₁ o₂ tape s q weights k acc)
                  ObservationCursor.bitCursor (by intro tape k; rfl)
                  (fun c j => attempt_success_interval r o₁ o₂ s q weights c j) ks middle
                exact (hreplay tape final hproj.symm).1
              refine ⟨step.2, hp.2.symm.le.trans (hmono.trans hfinal), ?_, ?_⟩
              · exact congrArg some (Prod.ext ha rfl)
              · exact ⟨middle, final, by simpa only [ha] using hr, hfinal, htail⟩
      have hbound := stopped_next_bound head t f
        (ChainStepIntervalReplay.chainStep_success_interval r o₁ o₂ s.drawTrials
          q weights current.state head.length) a E
        (continuationWeight P a rest) (continuationWeight_nonneg P a rest) (by
          intro stop hstart hstop pref hf
          have hpref : (head ++ pref.val).length = stop := by
            simp only [List.length_append, pref.2]
            omega
          have hbudget : (head ++ pref.val).length + (t - (stop-head.length)) =
              head.length+t := by rw [hpref]; omega
          have ha : (classifyState a).val ≠ .invalid :=
            ChainStepNoninvalid.chainStep_noninvalid r o₁ o₂ _ s.drawTrials q weights
              current.state head.length (a,stop) hvalid hf
          cases hr : (recordObservation r o₁ o₂ s.ρ
              ⟨a,stop,current.counts,current.numeratorSum⟩).val with
          | none =>
            have hz : fairMass (head ++ pref.val) (t - (stop-head.length))
                (fun tape => E tape stop) = 0 := by
              unfold fairMass
              simp [E, hr]
            rw [hz]
            exact continuationWeight_nonneg P a rest
          | some middle =>
            have hp := record_preserves r o₁ o₂ s.ρ _ middle hr
            have hi := ih hks rest hrest (head ++ pref.val) (t - (stop-head.length))
              middle (hp.2.trans hpref.symm) (by simpa only [hp.1] using ha)
            have heq : fairMass (head ++ pref.val) (t - (stop-head.length))
                (fun tape => E tape stop) =
              fairMass (head ++ pref.val) (t - (stop-head.length))
                (fun tape => ∃ final : ObservationCursor n,
                  final.bitCursor ≤ (head ++ pref.val).length + (t-(stop-head.length)) ∧
                  recordedObservationTrace r o₁ o₂ tape s q weights ks (some middle) =
                    some (final,rest)) := by
              unfold fairMass
              apply Finset.sum_congr rfl
              intro bits _
              rw [hbudget]
              simp [E, hr]
            rw [heq]
            simpa only [hp.1] using hi)
      calc
        _ ≤ fairMass head t (fun tape => ∃ stop, stop ≤ head.length+t ∧
            f tape = some (a,stop) ∧ E tape stop) := fairMass_mono head t _ _ hevent
        _ ≤ fairMass head t (fun tape => ∃ stop, stop ≤ head.length+t ∧
            f tape = some (a,stop)) * continuationWeight P a rest := hbound
        _ ≤ P current.state a * continuationWeight P a rest :=
          mul_le_mul_of_nonneg_right (hstep head t current.state a
            (classified_card _ hvalid) hvalid) (continuationWeight_nonneg P a rest)
        _ = _ := rfl

end CountingMatroid.Analysis.RecordedTraceContinuationBound
