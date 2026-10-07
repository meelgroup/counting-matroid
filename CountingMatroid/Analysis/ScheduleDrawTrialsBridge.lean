import CountingMatroid.Model.Program

set_option autoImplicit false

namespace CountingMatroid.Analysis.ScheduleDrawTrialsBridge

open CountingMatroid.Model
open CountingMatroid.Model.Operations

/-- INTERNAL: A search counter increases by at most one per successful iteration. -/
private theorem firstCounter_foldlWhile_le {α β : Type}
    (f : (ℕ × β) → α → Arlib.Computation.Charged Op Cell (Option (ℕ × β)))
    (hstep : ∀ b a b', (f b a).val = some b' → b'.1 ≤ b.1 + 1)
    (l : List α) (b : ℕ × β) :
    (Arlib.Computation.Charged.foldlWhile f l b).val.1 ≤ b.1 + l.length := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    cases h : (f b a).val with
    | none =>
      simp only [Arlib.Computation.Charged.val] at h
      simp [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val, h]
    | some b' =>
      have hs := hstep b a b' h
      have hr := ih b'
      simp only [Arlib.Computation.Charged.val] at h
      simp only [Arlib.Computation.Charged.foldlWhile, Arlib.Computation.Charged.val,
        h, List.length_cons] at *
      omega

/-- INTERNAL: The charged draw-trial search cannot exceed its loop cap.
TEXLINE: main.tex:1397-1421 -/
private theorem leastDrawTrials_val_le_cap (M : ℕ) :
    (CountingMatroid.Program.leastDrawTrials M).val ≤ M.log2 + 9 := by
  unfold CountingMatroid.Program.leastDrawTrials
  simp only [Arlib.Computation.Charged.val_bind,
    CountingMatroid.Model.Operations.binaryLoopBound,
    Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure]
  unfold Arlib.Computation.Charged.repeatWhile
  convert firstCounter_foldlWhile_le (f := _) ?_ (List.range (M.log2 + 8))
    (1, 2) using 1 <;> simp
  case e'_4 => omega
  intro b a b' b'q h
  split at h
  · simp only [successor, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_map, Arlib.Computation.Charged.val_op,
      natMul] at h
    cases h
    omega
  · simp at h

/-- INTERNAL: The field relation needed for the schedule trial bound. -/
private def drawCapGood (s : AnnealingSchedule) : Prop :=
  s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9

/-- INTERNAL: A property of the continuation value holds after a charged bind. -/
private theorem val_bind_property {α β : Type}
    (c : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β)
    (P : β → Prop) (h : ∀ x, P (f x).val) : P (c >>= f).val := by
  simpa only [Arlib.Computation.Charged.val_bind] using h c.val

/-- INTERNAL: The final schedule steps store the capped trial count.
TEXLINE: main.tex:1397-1421 -/
private theorem schedule_tail_good (bε : ℕ) (rho : ℚ) (L : ℕ) (eta : ℚ)
    (tau restartCap observations : ℕ) (p : InputParams) :
    drawCapGood (do
      let attemptsAndObservations ← natAdd restartCap observations
      let threeL ← natMul 3 L
      let drawCalls ← natMul threeL attemptsAndObservations
      let drawTrials ← CountingMatroid.Program.leastDrawTrials drawCalls
      let bδ ← CountingMatroid.Program.leastHalvings p.δ
      let tenBδ ← natMul 10 bδ
      let repetitions ← successor tenBδ
      pure (AnnealingSchedule.mk bε rho L eta tau restartCap observations
        drawCalls drawTrials bδ repetitions) :
        Arlib.Computation.Charged Op Cell AnnealingSchedule).val := by
  simp only [Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_pure,
    natAdd, natMul, Arlib.Computation.Charged.val_op, drawCapGood]
  exact leastDrawTrials_val_le_cap _

/-- INTERNAL: The schedule's trial count is controlled by its charged draw-call count.
TEXLINE: main.tex:1397-1421 -/
theorem schedule_drawTrials_le_drawCalls (n : ℕ) (p : InputParams) :
    let s := (CountingMatroid.Program.schedule n p).val
    s.drawTrials ≤ (3 * s.L * (s.restartCap + s.observations)).log2 + 9 := by
  change drawCapGood (CountingMatroid.Program.schedule n p).val
  unfold CountingMatroid.Program.schedule
  iterate 29
    apply val_bind_property
    intro
  exact schedule_tail_good _ _ _ _ _ _ _ p

end CountingMatroid.Analysis.ScheduleDrawTrialsBridge

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · peeled the schedule's charged binds and bounded the final trial counter by its loop cap; full schedule reduction stalled.
-/
