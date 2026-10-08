import CountingMatroid.Model.Program

set_option autoImplicit false

/-!
Deterministic locality of bounded rejection sampling. The cursor increases
monotonically, and agreement on the bits actually consumed determines the
whole value, including a rejected draw. No fair-bit law is assumed here.
-/

namespace CountingMatroid.Analysis.BoundedUniformReplay
open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Cursor monotonicity and replay from the consumed half-open interval.
TEXLINE: main.tex:1392-1421 -/
def IntervalReplay {α : Type} (f : (ℕ → Bool) → α) (cursor : α → ℕ)
    (start : ℕ) : Prop :=
  ∀ tape, start ≤ cursor (f tape) ∧
    ∀ other, (∀ i, start ≤ i → i < cursor (f tape) → tape i = other i) →
      f other = f tape

/-- INTERNAL: Compose two deterministic tape operations, restricting agreement
to each successive consumed interval. -/
theorem intervalReplay_comp {α β : Type} (f : (ℕ → Bool) → α)
    (g : (ℕ → Bool) → α → β) (ca : α → ℕ) (cb : β → ℕ) (start : ℕ)
    (hf : IntervalReplay f ca start)
    (hg : ∀ a, IntervalReplay (fun tape => g tape a) cb (ca a)) :
    IntervalReplay (fun tape => g tape (f tape)) cb start := by
  intro tape
  have hfirst := hf tape
  have hsecond := hg (f tape) tape
  refine ⟨hfirst.1.trans hsecond.1, ?_⟩
  intro other hagree
  change g other (f other) = g tape (f tape)
  rw [hfirst.2 other (fun i hlo hhi => hagree i hlo (hhi.trans_le hsecond.1))]
  exact hsecond.2 other (fun i hlo hhi => hagree i (hfirst.1.trans hlo) hhi)

/-- INTERNAL: A charged fold of monotone interval-local operations is itself
monotone and interval-local. -/
theorem foldl_intervalReplay {α β : Type}
    (f : (ℕ → Bool) → β → α → Arlib.Computation.Charged Op Cell β)
    (cursor : β → ℕ)
    (hstep : ∀ b a, IntervalReplay (fun tape => (f tape b a).val) cursor (cursor b))
    (xs : List α) (b : β) :
    IntervalReplay (fun tape => (Arlib.Computation.Charged.foldl (f tape) xs b).val)
      cursor (cursor b) := by
  induction xs generalizing b with
  | nil => exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
  | cons a xs ih =>
      exact intervalReplay_comp (fun tape => (f tape b a).val)
        (fun tape b' => (Arlib.Computation.Charged.foldl (f tape) xs b').val)
        cursor cursor (cursor b) (hstep b a) ih

/-- INTERNAL: Every bounded uniform draw replays on its consumed interval,
even when the rejection cap is exhausted. In particular its ending cursor
never precedes its starting cursor.
TEXLINE: main.tex:1392-1421 -/
theorem boundedUniform_interval_replay (trials v start : ℕ) :
    IntervalReplay (fun tape => (boundedUniform tape trials v start).val)
      Prod.snd start := by
  unfold boundedUniform
  simp only [Arlib.Computation.Charged.val_bind, lessThan, uniformWidth,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure, decide_eq_true_eq]
  by_cases hbad : v < 1
  · simp only [hbad, decide_true, ite_true, Arlib.Computation.Charged.val_pure]
    exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
  · simp only [hbad, decide_false, Bool.false_eq_true, ite_false,
      Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_op]
    by_cases hsingle : v < 2
    · simp only [hsingle, decide_true, ite_true, Arlib.Computation.Charged.val_pure]
      exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
    · simp only [hsingle, decide_false, Bool.false_eq_true, ite_false,
        Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.repeatFor]
      apply foldl_intervalReplay
      intro acc index
      simp only [Arlib.Computation.Charged.val_bind, isSome,
        Arlib.Computation.Charged.val_op]
      by_cases hdone : acc.1.isSome = true
      · simp only [hdone, ite_true, Arlib.Computation.Charged.val_pure]
        exact fun _ => ⟨le_rfl, fun _ _ => rfl⟩
      · simp only [hdone, Bool.false_eq_true, ite_false, Arlib.Computation.Charged.val_bind,
          Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure, decide_eq_true_eq]
        have htrial : IntervalReplay (fun tape =>
            (Arlib.Computation.Charged.repeatFor (fun _ (inner : ℕ × ℕ) => do
              let bit ← fairBit tape inner.2
              let value ← appendBit inner.1 bit
              let next ← successor inner.2
              pure (value, next)) ((v - 1).log2 + 1) (0, acc.2)).val)
            Prod.snd acc.2 := by
          apply foldl_intervalReplay
          intro inner i tape
          simp only [Arlib.Computation.Charged.val_bind, fairBit, appendBit, successor,
            Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure, decide_eq_true_eq]
          refine ⟨Nat.le_succ _, ?_⟩
          intro other hagree
          change (2 * inner.1 + if other inner.2 then 1 else 0, inner.2 + 1) = _
          rw [hagree inner.2 le_rfl (Nat.lt_succ_self _)]
          rfl
        intro tape
        have ht := htrial tape
        dsimp only
        simp only [Arlib.Computation.Charged.val_pure, apply_ite, ite_self]
        refine ⟨ht.1, ?_⟩
        intro other hagree
        have heq := ht.2 other hagree
        dsimp only at heq ⊢
        simp only [Arlib.Computation.Charged.repeatFor] at heq
        simp only [heq]
        split <;> simp_all only [ite_true, ite_false]

end CountingMatroid.Analysis.BoundedUniformReplay

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r21 · proved · monotone interval replay for every bounded rejection outcome,
  by nested charged-fold induction, including exhausted rejection caps.
-/
