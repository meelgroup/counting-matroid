import CountingMatroid.Analysis.BoundedUniformReplay

set_option autoImplicit false

/-!
Success-path replay for the charged chain step. A successful transition has
a monotone cursor and depends only on its consumed bit interval. The generic
option-fold lemma also retains the program's absorbing abort state.
-/

namespace CountingMatroid.Analysis.ChainStepIntervalReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformReplay

/-- INTERNAL: Success-path interval replay when aborted outcomes discard their
cursor. This does not assert replay of an aborted outcome. -/
def SuccessReplay {α : Type} (f : (ℕ → Bool) → Option α)
    (cursor : α → ℕ) (start : ℕ) : Prop :=
  ∀ tape out, f tape = some out → start ≤ cursor out ∧
    ∀ other, (∀ i, start ≤ i → i < cursor out → tape i = other i) →
      f other = some out

/-- INTERNAL: Composition of two successful tape operations retains interval
replay; a successful composition cannot have aborted in its first operation. -/
theorem successReplay_bind {α β : Type} (f : (ℕ → Bool) → Option α)
    (g : (ℕ → Bool) → α → Option β) (ca : α → ℕ) (cb : β → ℕ) (start : ℕ)
    (hf : SuccessReplay f ca start)
    (hg : ∀ a, SuccessReplay (fun tape => g tape a) cb (ca a)) :
    SuccessReplay (fun tape => (f tape).bind (g tape)) cb start := by
  intro tape out h
  cases hfirst : f tape with
  | none => simp +instances only [hfirst, Option.bind_none] at h; contradiction
  | some middle =>
    simp +instances only [hfirst, Option.bind_some] at h
    have ha := hf tape middle hfirst
    have hb := hg middle tape out h
    refine ⟨ha.1.trans hb.1, ?_⟩
    intro other hagree
    change (f other).bind (g other) = some out
    rw [ha.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hb.1))]
    exact hb.2 other (fun i hlo hhi => hagree i (ha.1.trans hlo) hhi)

/-- INTERNAL: Lift success-path replay through an option-valued charged fold
whose abort state is absorbing. -/
theorem foldl_successReplay {α β : Type}
    (f : (ℕ → Bool) → Option β → α → Arlib.Computation.Charged Op Cell (Option β))
    (cursor : β → ℕ)
    (hnone : ∀ tape a, (f tape none a).val = none)
    (hstep : ∀ b a, SuccessReplay (fun tape => (f tape (some b) a).val)
      cursor (cursor b)) (xs : List α) (b : β) :
    SuccessReplay (fun tape =>
      (Arlib.Computation.Charged.foldl (f tape) xs (some b)).val) cursor (cursor b) := by
  have habort (tape : ℕ → Bool) (ys : List α) :
      (Arlib.Computation.Charged.foldl (f tape) ys none).val = none := by
    induction ys with
    | nil => rfl
    | cons a ys ih => rw [Arlib.Computation.Charged.val_foldl_cons, hnone, ih]
  induction xs generalizing b with
  | nil =>
      intro tape out h
      have hb := Option.some.inj h
      subst out
      exact ⟨le_rfl, fun _ _ => rfl⟩
  | cons a xs ih =>
      have heq : (fun tape =>
          (Arlib.Computation.Charged.foldl (f tape) (a :: xs) (some b)).val) =
          (fun tape => ((f tape (some b) a).val).bind (fun middle =>
            (Arlib.Computation.Charged.foldl (f tape) xs (some middle)).val)) := by
        funext tape
        rw [Arlib.Computation.Charged.val_foldl_cons]
        cases hs : (f tape (some b) a).val with
        | none => exact habort tape xs
        | some middle => rfl
      rw [heq]
      exact successReplay_bind _ _ cursor cursor (cursor b) (hstep b a) ih

/-- INTERNAL: A successful underlying chain transition reads only its consumed
interval and never moves the fair-bit cursor backwards.
TEXLINE: main.tex:746-768,1392-1421 -/
theorem chainStep_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ)
    (weights : Multipliers n) (state : PairedSet n) (start : ℕ) :
    SuccessReplay (fun tape => (chainStep r o₁ o₂ tape trials q weights state start).val)
      Prod.snd start := by
  intro tape out hrun
  unfold chainStep at hrun ⊢
  simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
    Arlib.Computation.Charged.val_op] at hrun
  cases hhold : tape start with
  | true =>
      simp +instances only [hhold, ite_true, Arlib.Computation.Charged.val_pure] at hrun
      have hout : (state, start + 1) = out := Option.some.inj hrun
      subst out
      refine ⟨Nat.le_succ _, ?_⟩
      intro other hagree
      have hb : other start = true := (hagree start le_rfl (Nat.lt_succ_self _)).symm.trans hhold
      simp +instances only [chainStep, Arlib.Computation.Charged.val_bind, fairBit, successor,
        Arlib.Computation.Charged.val_op, hb, ite_true, Arlib.Computation.Charged.val_pure]
  | false =>
      simp +instances only [hhold, Bool.false_eq_true, ite_false] at hrun
      cases hdrawA : (boundedUniform tape trials n (start + 1)).val with
      | mk choiceA stopA =>
        cases choiceA with
        | none =>
          simp +instances only [hdrawA, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure] at hrun
          contradiction
        | some aIndex =>
          simp +instances only [hdrawA, Arlib.Computation.Charged.val_bind] at hrun
          cases hdrawB : (boundedUniform tape trials n stopA).val with
          | mk choiceB stopB =>
            cases choiceB with
            | none =>
              simp +instances only [hdrawB, Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure] at hrun
              contradiction
            | some bIndex =>
              simp +instances only [hdrawB, Arlib.Computation.Charged.val_bind] at hrun
              have hA := boundedUniform_interval_replay trials n (start + 1) tape
              have hB := boundedUniform_interval_replay trials n stopA tape
              simp +instances only [hdrawA] at hA
              simp +instances only [hdrawB] at hB
              have hstartB : start ≤ stopB := (Nat.le_succ _).trans (hA.1.trans hB.1)
              have replayDraws (other : ℕ → Bool)
                  (hstop : stopB ≤ out.2)
                  (hagree : ∀ i, start ≤ i → i < out.2 → tape i = other i) :
                  other start = false ∧
                  (boundedUniform other trials n (start + 1)).val = (some aIndex, stopA) ∧
                  (boundedUniform other trials n stopA).val = (some bIndex, stopB) := by
                refine ⟨?_, ?_, ?_⟩
                · exact (hagree start le_rfl (by omega)).symm.trans hhold
                · exact hA.2 other (fun i hlo hhi => hagree i (by omega) (by omega))
                · exact hB.2 other (fun i hlo hhi => hagree i (by omega) (by omega))
              -- Selection/classification/weight tests read no tape. At each
              -- successful leaf, the final cursor is stopB or the acceptance
              -- draw's ending cursor, and replayDraws fixes both index draws.
              split at hrun
              · rename_i optionA optionB a b hSelA hSelB
                simp +instances only [Arlib.Computation.Charged.val_bind, erasePaired, insertPaired,
                  Arlib.Computation.Charged.val_opMany] at hrun
                split at hrun
                · have hout := Option.some.inj hrun
                  have hstop : stopB ≤ out.2 := by rw [← hout]
                  refine ⟨hstartB.trans hstop, ?_⟩
                  intro other hagree
                  obtain ⟨hb, hdA, hdB⟩ := replayDraws other hstop hagree
                  simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
                    Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false,
                    hdA, hdB, erasePaired, insertPaired, Arlib.Computation.Charged.val_opMany]
                  simp +instances only [*, Arlib.Computation.Charged.val_bind,
                    Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.val_opMany]
                · simp +instances only [Arlib.Computation.Charged.val_bind] at hrun
                  split at hrun
                  · rename_i oldWeight newWeight hOld hNew
                    simp +instances only [Arlib.Computation.Charged.val_bind] at hrun
                    by_cases hneed : (ratLess (ratDiv newWeight oldWeight).val 1).val = true
                    · rw [if_pos hneed] at hrun
                      simp +instances only [Arlib.Computation.Charged.val_bind,
                        ratDiv, rationalDenominator, rationalNumerator,
                        Arlib.Computation.Charged.val_opMany] at hrun
                      cases hdrawC : (boundedUniform tape trials
                          (newWeight / oldWeight).den stopB).val with
                      | mk choiceC stopC =>
                        cases choiceC with
                        | none =>
                          simp +instances only [hdrawC, Arlib.Computation.Charged.val_bind,
                            Arlib.Computation.Charged.val_pure] at hrun
                          contradiction
                        | some value =>
                          simp +instances only [hdrawC, Arlib.Computation.Charged.val_bind] at hrun
                          have hC := boundedUniform_interval_replay trials
                            (newWeight / oldWeight).den stopB tape
                          simp +instances only [hdrawC] at hC
                          split at hrun
                          all_goals
                            have hout := Option.some.inj hrun
                            have hstop : stopC = out.2 := by rw [← hout]
                            have hstopB : stopB ≤ out.2 := hstop ▸ hC.1
                            refine ⟨hstartB.trans hstopB, ?_⟩
                            intro other hagree
                            obtain ⟨hb, hdA, hdB⟩ := replayDraws other hstopB hagree
                            have hdC := hC.2 other (fun i hlo hhi => hagree i
                              (hstartB.trans hlo) (by omega))
                            simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
                              Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false,
                              hdA, hdB, erasePaired, insertPaired]
                            simp +instances only [*, Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_opMany]
                            simp +instances only [*, Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_op,
                              ratDiv, rationalDenominator, rationalNumerator]
                            simp +instances only [*, Arlib.Computation.Charged.val_bind,
                              Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure,
                              Bool.false_eq_true, ite_true, ite_false]
                            simpa only [← hstop] using congrArg some hout
                    · rw [if_neg hneed] at hrun
                      have hout := Option.some.inj hrun
                      have hstop : stopB ≤ out.2 := by rw [← hout]
                      refine ⟨hstartB.trans hstop, ?_⟩
                      intro other hagree
                      obtain ⟨hb, hdA, hdB⟩ := replayDraws other hstop hagree
                      simp +instances only [Arlib.Computation.Charged.val_bind, fairBit, successor,
                        Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false,
                        hdA, hdB, erasePaired, insertPaired]
                      simp +instances only [*, Arlib.Computation.Charged.val_bind,
                        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
                      simp only [Bool.false_eq_true, ite_false, Arlib.Computation.Charged.val_pure]
                  · cases hrun
              · simp +instances only [Arlib.Computation.Charged.val_pure] at hrun
                contradiction

end CountingMatroid.Analysis.ChainStepIntervalReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · success-path replay for chainStep, by composing the hold bit,
  two index draws and optional rational acceptance draw. Kept charged Boolean
  tests intact while splitting branches to preserve their decidable instances.
-/
