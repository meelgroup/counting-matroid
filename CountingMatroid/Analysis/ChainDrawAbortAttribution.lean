import CountingMatroid.Analysis.ChainDrawSiteReplay
import CountingMatroid.Analysis.InitialMultipliersGood
import CountingMatroid.Analysis.BoundedUniformAbortMass
import CountingMatroid.Analysis.ClassifiedStateSelection

set_option autoImplicit false

/-!
Abort attribution for a chain attempt from a non-invalid state. Successful
bounded draws return in-range indices, classified states have weight values,
and the imported selection correctness invariant excludes failed lookups.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: A successful bounded draw is below its denominator. -/
theorem boundedUniform_result_lt (tape : ℕ → Bool) (trials v cursor value : ℕ)
    (h : (boundedUniform tape trials v cursor).val.1 = some value) : value < v := by
  by_cases hv : 2 ≤ v
  · rw [BoundedUniformAbortMass.boundedUniform_value tape trials v cursor hv] at h
    have hs (k : ℕ) (acc : Option ℕ × ℕ)
        (ha : ∀ a, acc.1 = some a → a < v) :
        ∀ a, (BoundedUniformAbortMass.sampleWords tape v k acc).1 = some a → a < v := by
      induction k generalizing acc with
      | zero => exact ha
      | succ k ih =>
          rw [BoundedUniformAbortMass.sampleWords]
          split
          · exact ih acc ha
          · dsimp only
            split
            · rename_i hlt
              apply ih
              intro a heq
              cases Option.some.inj heq
              exact hlt
            · apply ih
              intro a heq
              cases heq
    exact hs trials (none, cursor) (by intro a heq; cases heq) value h
  · unfold boundedUniform at h
    simp only [Arlib.Computation.Charged.val_bind, Model.Operations.lessThan,
      Arlib.Computation.Charged.val_op, decide_eq_true_eq] at h
    split at h
    · cases h
    · rename_i hpos
      simp only [Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_op, decide_eq_true_eq] at h
      rw [if_pos (by omega : v < 2)] at h
      have heq : 0 = value := Option.some.inj h
      omega

/-- INTERNAL: A classified defect label is off the diagonal. -/
theorem classified_defect_distinct {n : ℕ} (state : PairedSet n)
    (i j : Fin n) (hk : (classifyState state).val = .defect i j) : i ≠ j := by
  intro hij
  subst j
  unfold classifyState at hk
  simp only [Arlib.Computation.Charged.val_bind] at hk
  split at hk
  · cases hk
  · split at hk
    · cases hk
    · simp only [Arlib.Computation.Charged.val_bind] at hk
      rename_i a b he hb
      by_cases hequal : (Model.Operations.indexEqual a b).val = true
      · rw [if_pos hequal] at hk
        cases hk
      · rw [if_neg hequal] at hk
        have heq := StateKind.defect.inj hk
        have hab : a = b := heq.1.trans heq.2.symm
        apply hequal
        simp [Model.Operations.indexEqual, hab]

    · cases hk

/-- INTERNAL: A non-invalid classifier always has an actual weight value. -/
theorem classified_weight_exists {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (hvalid : (classifyState state).val ≠ .invalid) :
    ∃ w, (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val = some w := by
  cases hk : (classifyState state).val with
  | invalid => exact False.elim (hvalid hk)
  | transversal =>
      simp only [weightOfKind, Arlib.Computation.Charged.val_bind]
      exact ⟨_, rfl⟩
  | defect i j =>
      have hne := classified_defect_distinct state i j hk
      simp only [weightOfKind, dif_pos hne, Arlib.Computation.Charged.val_bind]
      exact ⟨_, rfl⟩

/-- INTERNAL: On a non-invalid state, a failed chain attempt is attributable
to one of its three actual capped draws, with the descriptor stopped before
that draw. No positivity or accuracy property of the weights is required.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem chain_abort_draw_site {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ)
    (hvalid : (classifyState state).val ≠ .invalid)
    (habort : (chainStep r o₁ o₂ tape s.drawTrials q weights state cursor).val = none) :
    ∃ site d, chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d ∧
      (boundedUniform tape s.drawTrials d.2 d.1).val.1 = none := by
  unfold chainStep at habort
  simp only [Arlib.Computation.Charged.val_bind,
    Model.Operations.fairBit, Model.Operations.successor,
    Arlib.Computation.Charged.val_op] at habort
  cases hhold : tape cursor with
  | true =>
      simp only [hhold, ite_true, Arlib.Computation.Charged.val_pure] at habort
      cases habort
  | false =>
      simp only [hhold, Bool.false_eq_true, ite_false] at habort
      cases hA : (boundedUniform tape s.drawTrials n (cursor + 1)).val with
      | mk choiceA stopA =>
        cases choiceA with
        | none =>
          refine ⟨⟨0, by decide⟩, (cursor + 1, n), ?_, ?_⟩
          · simp [chainDrawSite, hhold]
          · exact congrArg Prod.fst hA
        | some aIndex =>
          simp only [hA, Arlib.Computation.Charged.val_bind] at habort
          cases hB : (boundedUniform tape s.drawTrials n stopA).val with
          | mk choiceB stopB =>
            cases choiceB with
            | none =>
              refine ⟨⟨1, by decide⟩, (stopA, n), ?_, ?_⟩
              · simp [chainDrawSite, hhold, hA]
              · exact congrArg Prod.fst hB
            | some bIndex =>
              have haIndex := boundedUniform_result_lt tape s.drawTrials n
                (cursor + 1) aIndex (by rw [hA])
              have hbIndex := boundedUniform_result_lt tape s.drawTrials n
                stopA bIndex (by rw [hB])
              obtain ⟨a, ha⟩ := ClassifiedStateSelection.classified_state_selection
                state hvalid true aIndex haIndex
              obtain ⟨b, hb⟩ := ClassifiedStateSelection.classified_state_selection
                state hvalid false bIndex hbIndex
              simp only [hB, Arlib.Computation.Charged.val_bind, ha, hb,
                Model.Operations.erasePaired, Model.Operations.insertPaired,
                Arlib.Computation.Charged.val_opMany] at habort
              let candidate : PairedSet n := insert b (state.erase a)
              change (match (classifyState candidate).val with
                | .invalid => pure (some (state, stopB))
                | _ => _ : Arlib.Computation.Charged Model.Operations.Op
                  Model.Operations.Cell (Option (PairedSet n × ℕ))).val = none at habort
              cases hkind : (classifyState candidate).val
              case invalid =>
                simp only [hkind, Arlib.Computation.Charged.val_pure] at habort
                cases habort
              all_goals
                have hnewvalid : (classifyState candidate).val ≠ .invalid := by
                  rw [hkind]
                  intro h
                  cases h
                obtain ⟨oldWeight, ho⟩ := classified_weight_exists
                  r o₁ o₂ q weights state hvalid
                obtain ⟨newWeight, hn⟩ := classified_weight_exists
                  r o₁ o₂ q weights candidate hnewvalid
                have hnKind := hn
                rw [hkind] at hnKind
                have hkRaw := hkind
                dsimp only [candidate] at hkRaw hnKind
                simp only [hkind, hkRaw, Arlib.Computation.Charged.val_bind,
                  ho, hnKind] at habort
                by_cases hneed : (Model.Operations.ratLess
                    (Model.Operations.ratDiv newWeight oldWeight).val 1).val = true
                · rw [if_pos hneed] at habort
                  have hneedProp : newWeight / oldWeight < 1 := by
                    with_unfolding_all
                      exact of_decide_eq_true hneed
                  simp only [Arlib.Computation.Charged.val_bind,
                    Model.Operations.ratDiv,
                    Model.Operations.rationalDenominator,
                    Model.Operations.rationalNumerator,
                    Arlib.Computation.Charged.val_opMany] at habort
                  cases hC : (boundedUniform tape s.drawTrials
                      (newWeight / oldWeight).den stopB).val with
                  | mk choiceC stopC =>
                    cases choiceC with
                    | none =>
                      refine ⟨⟨2, by decide⟩, (stopB, (newWeight / oldWeight).den), ?_, ?_⟩
                      · simp only [chainDrawSite, hhold, Bool.false_eq_true, ite_false,
                          hA, hB, ha, hb, Option.bind_eq_bind, Option.bind_some]
                        change (if (classifyState candidate).val = .invalid then none else _) = _
                        rw [if_neg hnewvalid]
                        have hnRaw := hn
                        dsimp only [candidate] at hnRaw
                        simp only [Model.Operations.erasePaired, Model.Operations.insertPaired,
                          Arlib.Computation.Charged.val_opMany, ho, hnRaw,
                          Option.bind_eq_bind, Option.bind_some,
                          hneedProp, ite_true]
                      · exact congrArg Prod.fst hC
                    | some value =>
                      simp only [hC, Arlib.Computation.Charged.val_bind] at habort
                      split at habort <;> cases habort
                · rw [if_neg hneed] at habort
                  cases habort

end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · closed · imported selector correctness is now proved; all abort attribution dependencies are closed.
* r28 · composed · proved sampler output range, classifier off-diagonal labels, classified weight existence, and all chain abort branches using classified_state_selection. Selection correctness is the only remaining imported child obligation.
* r28 · open · unfolded the charged chain attempt and excluded the holding
  branch; the remaining branches need the boundedUniform output range and
  executable selection correctness for classifier-valid states, followed by
  exclusion of diagonal defect weight failures.
-/
