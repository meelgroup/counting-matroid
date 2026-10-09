import CountingMatroid.Analysis.ChainStepIntervalReplay

set_option autoImplicit false

/-!
Pre-draw descriptors for a chain attempt. They record the next capped draw's
cursor and denominator without reading any bits of that draw.
-/

namespace CountingMatroid.Analysis.ObservationRoundDrawSites
open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: Stop before one of the three actual capped draws in a chain
attempt. No bits of the reported draw itself have been inspected.
TEXLINE: main.tex:746-751,1392-1421 -/
noncomputable def chainDrawSite {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) (site : Fin 3) : Option (ℕ × ℕ) := do
  if tape cursor then none else
    let cursor := cursor + 1
    if site.val = 0 then some (cursor, n) else
      let selected := (boundedUniform tape s.drawTrials n cursor).val
      let aIndex ← selected.1
      if site.val = 1 then some (selected.2, n) else
        let selectedOut := (boundedUniform tape s.drawTrials n selected.2).val
        let bIndex ← selectedOut.1
        let a ← (selectPaired state true aIndex).val
        let b ← (selectPaired state false bIndex).val
        let candidate := (Model.Operations.insertPaired
          (Model.Operations.erasePaired state a).val b).val
        let newKind := (classifyState candidate).val
        if newKind = .invalid then none else
          let oldKind := (classifyState state).val
          let oldWeight ← (weightOfKind r o₁ o₂ q weights state oldKind).val
          let newWeight ← (weightOfKind r o₁ o₂ q weights candidate newKind).val
          let ratio := newWeight / oldWeight
          if ratio < 1 then some (selectedOut.2, ratio.den) else none

/-- INTERNAL: Every stopped draw descriptor has a positive denominator
when the original ground is nonempty.
TEXLINE: main.tex:1392-1421 -/
theorem chainDrawSite_positive {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) (site : Fin 3) (d : ℕ × ℕ)
    (hn : 0 < n) (h : chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d) :
    0 < d.2 := by
  have hden (a : ℚ) : 0 < a.den := Rat.den_pos a
  unfold chainDrawSite at h
  split at h
  · cases h
  · split at h
    · cases Option.some.inj h
      exact hn
    · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨aIndex, ha, h⟩ := h
      split at h
      · cases Option.some.inj h
        exact hn
      · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨bIndex, hb, a, ha', b, hb', h⟩ := h
        split at h
        · cases h
        · simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨oldWeight, ho, newWeight, hn', h⟩ := h
          split at h
          · cases Option.some.inj h
            exact hden _
          · cases h

/-- INTERNAL: A stopped chain draw has a monotone cursor and replays using
only the bits read before that draw, rather than its as-yet-unread trials.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem chainDrawSite_success_interval {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (q : ℚ)
    (weights : Multipliers n) (state : PairedSet n) (cursor : ℕ) (site : Fin 3) :
    ChainStepIntervalReplay.SuccessReplay
      (fun tape => chainDrawSite r o₁ o₂ tape s q weights state cursor site)
      Prod.fst cursor := by
  intro tape d h
  change chainDrawSite r o₁ o₂ tape s q weights state cursor site = some d at h
  unfold chainDrawSite at h
  split at h
  · cases h
  · rename_i hhold
    split at h
    · rename_i hzero
      have hd := Option.some.inj h
      subst d
      refine ⟨by omega, ?_⟩
      intro other hagree
      have hb : other cursor = tape cursor :=
        (hagree cursor le_rfl (by omega)).symm
      simp only [chainDrawSite, hb, hhold, hzero, Bool.false_eq_true, ite_false, ite_true]
    · rename_i hzero
      simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
      obtain ⟨aIndex, ha, h⟩ := h
      have hA := BoundedUniformReplay.boundedUniform_interval_replay
        s.drawTrials n (cursor + 1) tape
      dsimp only at hA
      split at h
      · rename_i hone
        have hd := Option.some.inj h
        subst d
        refine ⟨(Nat.le_succ cursor).trans hA.1, ?_⟩
        intro other hagree
        have hb : other cursor = tape cursor :=
          (hagree cursor le_rfl (by dsimp only; omega)).symm
        have heq := hA.2 other (fun i hlo hhi => hagree i (by omega) hhi)
        simp only [chainDrawSite, hb, hhold, hzero, Bool.false_eq_true,
          ite_false, heq, ha, Option.bind_eq_bind, Option.bind_some, hone, ite_true]
        simp
      · rename_i hone
        simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
        obtain ⟨bIndex, hbIndex, a, haSel, b, hbSel, h⟩ := h
        have hB := BoundedUniformReplay.boundedUniform_interval_replay
          s.drawTrials n (boundedUniform tape s.drawTrials n (cursor + 1)).val.2 tape
        dsimp only at hB
        split at h
        · cases h
        · rename_i hkind
          simp only [Option.bind_eq_bind, Option.bind_eq_some_iff] at h
          obtain ⟨oldWeight, ho, newWeight, hn, h⟩ := h
          split at h
          · rename_i hratio
            have hd := Option.some.inj h
            subst d
            have hstop : cursor + 1 ≤
                (boundedUniform tape s.drawTrials n
                  (boundedUniform tape s.drawTrials n (cursor + 1)).val.2).val.2 :=
              hA.1.trans hB.1
            refine ⟨(Nat.le_succ cursor).trans hstop, ?_⟩
            intro other hagree
            have hb : other cursor = tape cursor :=
              (hagree cursor le_rfl (by dsimp only; omega)).symm
            have heqA := hA.2 other (fun i hlo hhi =>
              hagree i (by omega) (hhi.trans_le hB.1))
            have heqB := hB.2 other (fun i hlo hhi =>
              hagree i ((Nat.le_succ cursor).trans (hA.1.trans hlo)) hhi)
            simp only [chainDrawSite, hb, hhold, hzero, hone,
              Bool.false_eq_true, ite_false, heqA, heqB, ha, hbIndex,
              haSel, hbSel, hkind, ho, hn, hratio,
              Option.bind_eq_bind, Option.bind_some, ite_true]
          · cases h

end CountingMatroid.Analysis.ObservationRoundDrawSites

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r28 · proved · all three stopped-draw replay branches, composing boundedUniform interval replay before each descriptor; no open proof remains in this file.
* r28 · open · retained the existing descriptor and positive-denominator
  proof under their original names; proved the hold-bit/site-0 locality
  branch. The remaining sites require composition of one or two
  boundedUniform_interval_replay results with deterministic option branches.
-/
