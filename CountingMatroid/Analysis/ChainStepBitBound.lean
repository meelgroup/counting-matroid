import CountingMatroid.Analysis.PhaseChainWork
import CountingMatroid.Analysis.ChainDrawSiteReplay

set_option autoImplicit false

namespace CountingMatroid.Analysis.ChainStepBitBound

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.ObservationRoundDrawSites

/-- INTERNAL: Sum a uniform cursor increment along an actual charged fold. -/
private theorem fold_cursor_growth {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β) (cursor : β → ℕ)
    (D : ℕ) (hf : ∀ b a, cursor (f b a).val ≤ cursor b + D)
    (xs : List α) (b : β) :
    cursor (Arlib.Computation.Charged.foldl f xs b).val ≤ cursor b + xs.length * D := by
  induction xs generalizing b with
  | nil => simp
  | cons a xs ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons]
      have h := ih (f b a).val
      have hs := hf b a
      simp only [List.length_cons, Nat.add_mul, Nat.one_mul]
      omega

/-- INTERNAL: All rejection trials together consume at most their cap times
the exact implementation width, including draws which abort.
TEXLINE: main.tex:1392-1421 -/
theorem boundedUniform_cursor_le (tape : ℕ → Bool) (trials v cursor : ℕ) :
    (boundedUniform tape trials v cursor).val.2 ≤
      cursor + trials * ((v - 1).log2 + 1) := by
  let width := (v - 1).log2 + 1
  have htrial (inner : ℕ × ℕ) :
      (Arlib.Computation.Charged.repeatFor (fun _ inner => do
        let bit ← fairBit tape inner.2
        let value ← appendBit inner.1 bit
        let next ← successor inner.2
        pure (value, next)) width inner).val.2 ≤ inner.2 + width := by
    simpa only [Arlib.Computation.Charged.repeatFor, List.length_range,
      Nat.mul_one] using fold_cursor_growth
        (fun inner (_ : ℕ) => do
          let bit ← fairBit tape inner.2
          let value ← appendBit inner.1 bit
          let next ← successor inner.2
          pure (value, next)) Prod.snd 1 (by intro b a; rfl)
        (List.range width) inner
  unfold boundedUniform
  simp only [Arlib.Computation.Charged.val_bind]
  split
  · simp only [Arlib.Computation.Charged.val_pure]; omega
  · simp only [Arlib.Computation.Charged.val_bind]
    split
    · simp only [Arlib.Computation.Charged.val_pure]; omega
    · simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
        uniformWidth, Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.repeatFor]
      apply (fold_cursor_growth _ Prod.snd width ?_ _ (none, cursor)).trans_eq
        (by simp only [List.length_range, width, Nat.mul_comm])
      intro acc index
      simp only [Arlib.Computation.Charged.val_bind]
      split
      · simp only [Arlib.Computation.Charged.val_pure]; omega
      · simp only [Arlib.Computation.Charged.val_bind]
        have ht := htrial (0, acc.2)
        split <;> exact ht

/-- INTERNAL: A capped draw width is bounded by the natural encoding length. -/
private theorem draw_width_le (v : ℕ) : (v - 1).log2 + 1 ≤ v.log2 + 1 := by
  simp only [Nat.log2_eq_log_two]
  exact Nat.add_le_add_right (Nat.log_mono_right (Nat.sub_le v 1)) 1

/-- INTERNAL: A ratio of two bounded state weights has a bounded draw width.
TEXLINE: main.tex:1382-1400 -/
private theorem ratio_width_le (old new : ℚ) (K : ℕ)
    (ho : binaryRatLength old ≤ 2 * K) (hn : binaryRatLength new ≤ 2 * K) :
    ((new / old).den - 1).log2 + 1 ≤ 4 * K := by
  have hr := binaryRatLength_div_le new old
  have hd := draw_width_le (new / old).den
  unfold binaryRatLength binaryNatLength at hr ho hn
  omega

set_option backward.isDefEq.respectTransparency false in
/-- INTERNAL: Every successful chain step consumes one laziness bit and at
most three capped draws of bounded width, uniformly in the state and tape.
TEXLINE: main.tex:1392-1421 -/
theorem chain_step_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (out : PairedSet n × ℕ)
    (h : (chainStep r o₁ o₂ tape trials q weights state cursor).val = some out) :
    out.2 ≤ cursor + (1 + 3 * trials * (4 * K + n + 1)) := by
  let W := 4 * K + n + 1
  have hnwidth : (n - 1).log2 + 1 ≤ W := by
    have hl : n.log2 ≤ n := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 n
    have hd := draw_width_le n
    dsimp [W]; omega
  have hdraw (v c : ℕ) (hv : (v - 1).log2 + 1 ≤ W) :
      (boundedUniform tape trials v c).val.2 ≤ c + trials * W :=
    (boundedUniform_cursor_le tape trials v c).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left trials hv) c)
  have hweight (x : PairedSet n) (kind : StateKind n) :=
    (PhaseChainWork.weightOfKind_work_size r o₁ o₂ q weights x kind K hq hw).2
  unfold chainStep at h
  dsimp only [Arlib.Computation.Charged.val_bind, fairBit, successor,
    Arlib.Computation.Charged.val_op] at h
  by_cases hh : tape cursor = true
  · rw [if_pos hh] at h
    have he := Option.some.inj h
    rw [← he]
    omega
  · rw [if_neg hh] at h
    simp +instances only [Arlib.Computation.Charged.val_bind] at h
    have hA := hdraw n (cursor + 1) hnwidth
    split at h
    · cases h
    · simp +instances only [Arlib.Computation.Charged.val_bind] at h
      have hB := hdraw n (boundedUniform tape trials n (cursor + 1)).val.2 hnwidth
      split at h
      · cases h
      · simp +instances only [Arlib.Computation.Charged.val_bind] at h
        split at h
        · simp +instances only [Arlib.Computation.Charged.val_bind, erasePaired, insertPaired,
            Arlib.Computation.Charged.val_opMany] at h
          split at h
          · have he := Option.some.inj h
            rw [← he]
            dsimp [W] at hA hB ⊢
            simp only [Nat.mul_assoc] at hA hB ⊢
            omega
          · simp +instances only [Arlib.Computation.Charged.val_bind] at h
            split at h
            · rename_i old new ho hn
              have hr := ratio_width_le old new K (hweight _ _ old ho) (hweight _ _ new hn)
              simp +instances only [Arlib.Computation.Charged.val_bind] at h
              split at h
              · simp +instances only [Arlib.Computation.Charged.val_bind, ratDiv,
                  rationalDenominator, rationalNumerator,
                  Arlib.Computation.Charged.val_opMany] at h
                have hC := hdraw (new / old).den
                  (boundedUniform tape trials n
                    (boundedUniform tape trials n (cursor + 1)).val.2).val.2
                  (by dsimp [W]; omega)
                split at h
                · cases h
                · simp +instances only [Arlib.Computation.Charged.val_bind] at h
                  split at h <;> have he := Option.some.inj h
                  all_goals rw [← he]; dsimp [W] at hA hB hC ⊢; simp only [Nat.mul_assoc] at hA hB hC ⊢; omega
              · have he := Option.some.inj h
                rw [← he]
                dsimp [W] at hA hB ⊢
                simp only [Nat.mul_assoc] at hA hB ⊢
                omega
            · cases h
        · cases h

/-- INTERNAL: Even all future trials of a stopped chain draw fit the same
three-draw budget as a completed chain attempt.
TEXLINE: main.tex:1392-1421 -/
theorem chain_draw_site_bit_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K)
    (site : Fin 3) (d : ℕ × ℕ)
    (h : chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d) :
    d.1 + s.drawTrials * ((d.2 - 1).log2 + 1) ≤
      cursor + (1 + 3 * s.drawTrials * (4 * K + n + 1)) := by
  let W := 4 * K + n + 1
  have hnwidth : (n - 1).log2 + 1 ≤ W := by
    have hl : n.log2 ≤ n := by
      simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 n
    have hd := draw_width_le n
    dsimp [W]; omega
  have hdraw (c : ℕ) : (boundedUniform tape s.drawTrials n c).val.2 ≤ c + s.drawTrials * W :=
    (boundedUniform_cursor_le tape s.drawTrials n c).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left s.drawTrials hnwidth) c)
  have hntrials := Nat.mul_le_mul_left s.drawTrials hnwidth
  have hweight (x : PairedSet n) (kind : StateKind n) :=
    (PhaseChainWork.weightOfKind_work_size r o₁ o₂ q weights x kind K hq hw).2
  unfold chainDrawSite at h
  split at h
  · cases h
  · have hA := hdraw (cursor + 1)
    split at h
    · have he := Option.some.inj h
      rw [← he]
      dsimp [W] at hntrials ⊢
      simp only [Nat.mul_assoc] at hntrials ⊢
      omega
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨aIndex, ha, h⟩ := h
      have hB := hdraw (boundedUniform tape s.drawTrials n (cursor + 1)).val.2
      split at h
      · have he := Option.some.inj h
        rw [← he]
        dsimp [W] at hA hntrials ⊢
        simp only [Nat.mul_assoc] at hA hntrials ⊢
        omega
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨bIndex, hb, a, ha', b, hb', h⟩ := h
        split at h
        · cases h
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨old, ho, new, hn, h⟩ := h
          have hr := ratio_width_le old new K (hweight _ _ old ho) (hweight _ _ new hn)
          have hrt := Nat.mul_le_mul_left s.drawTrials (hr.trans (show 4 * K ≤ 4 * K + n + 1 by omega))
          split at h
          · have he := Option.some.inj h
            rw [← he]
            dsimp [W] at hA hB ⊢
            simp only [Nat.mul_assoc] at hA hB ⊢
            omega
          · cases h

end CountingMatroid.Analysis.ChainStepBitBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* this round · proved capped-uniform cursor growth and chain/stopped-site three-draw bounds; avoided an ill-typed simplified charged Boolean condition with a local transparency setting.
-/
