import CountingMatroid.Analysis.PrimitiveOracleCalls
import CountingMatroid.Model.Program

set_option autoImplicit false

/-!
# Oracle charges in one capped annealing run

The bounds below sum the two supplied independence-oracle charges through
the capped loops, including abort branches.
-/

namespace CountingMatroid.Analysis.BoundedRunOracleCalls

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Uniform oracle charges add across a finite charged loop. -/
theorem oracleCalls_repeatFor_le {β : Type}
    {f : ℕ → β → Arlib.Computation.Charged Op Cell β} {k : ℕ}
    (h : ∀ j b, oracleCalls (f j b) ≤ k) (n : ℕ) (b : β) :
    oracleCalls (Arlib.Computation.Charged.repeatFor f n b) ≤ n * k := by
  have hfold : ∀ (l : List ℕ) (b : β),
      oracleCalls (Arlib.Computation.Charged.foldl (fun b j => f j b) l b) ≤
        l.length * k := by
    intro l
    induction l with
    | nil => intro b; simp [oracleCalls]
    | cons j js ih =>
        intro b
        have htail := ih (f j b).val
        have hhead := h j b
        simp only [List.length_cons]
        calc
          oracleCalls (Arlib.Computation.Charged.foldl
              (fun b j => f j b) (j :: js) b) =
              oracleCalls (f j b) +
                oracleCalls (Arlib.Computation.Charged.foldl
                  (fun b j => f j b) js (f j b).val) := by
                simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]
          _ ≤ k + js.length * k := Nat.add_le_add hhead htail
          _ = (js.length + 1) * k := by ring
  simpa [Arlib.Computation.Charged.repeatFor] using hfold (List.range n) b

open CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound

/-- INTERNAL: Returning a value makes no independence query. -/
@[local simp] theorem oracleCalls_pure_zero {α : Type} (x : α) :
    oracleCalls (pure x : Arlib.Computation.Charged Op Cell α) = 0 := by
  simp [oracleCalls]

/-- INTERNAL: A word instruction makes no independence query. -/
@[local simp] theorem oracleCalls_word_zero {α : Type}
    (op : Arlib.Computation.Op) (x : α) :
    oracleCalls (Arlib.Computation.Charged.op (Op.word op) x) = 0 := by
  simp [oracleCalls]

/-- INTERNAL: Repeated word instructions make no independence query. -/
@[local simp] theorem oracleCalls_many_zero {α : Type}
    (op : Arlib.Computation.Op) (k : ℕ) (x : α) :
    oracleCalls (Arlib.Computation.Charged.opMany (Op.word op) k x) = 0 := by
  simp [oracleCalls]

/-- INTERNAL: A state-independent continuation bound adds to the first charge. -/
theorem oracleCalls_bind_bound {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) (a b : ℕ)
    (hp : oracleCalls p ≤ a) (hf : ∀ x, oracleCalls (f x) ≤ b) :
    oracleCalls (p >>= f) ≤ a + b := by
  rw [oracleCalls_bind]
  exact Nat.add_le_add hp (hf p.val)

/-- INTERNAL: Early stopping cannot exceed a uniform charge per loop position. -/
theorem oracleCalls_foldlWhile_bound {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell (Option β)) (k : ℕ)
    (hf : ∀ b a, oracleCalls (f b a) ≤ k) (l : List α) (b : β) :
    oracleCalls (Arlib.Computation.Charged.foldlWhile f l b) ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp [oracleCalls]
  | cons a l ih =>
      cases h : (f b a).val with
      | none =>
          simp only [Arlib.Computation.Charged.val] at h
          simp only [Arlib.Computation.Charged.foldlWhile, h, List.length_cons]
          exact (hf b a).trans (by nlinarith)
      | some b' =>
          simp only [Arlib.Computation.Charged.val] at h
          simp only [Arlib.Computation.Charged.foldlWhile, h, List.length_cons]
          have hb := hf b a
          have hl := ih b'
          simp only [oracleCalls, Arlib.Computation.Charged.cost, Pi.add_apply] at hb hl ⊢
          nlinarith

/-- INTERNAL: Each exchange attempt evaluates at most two paired-state weights.
TEXLINE: main.tex:1333-1346 -/
theorem chainStep_calls_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (trials : ℕ) (q : ℚ) (w : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) :
    oracleCalls (chainStep r o₁ o₂ tape trials q w state cursor) ≤ 4 * n := by
  unfold chainStep
  simp only [oracleCalls_bind]
  have hb : oracleCalls (fairBit tape cursor) = 0 := by simp [fairBit, oracleCalls]
  simp only [hb, successor, oracleCalls_word_zero, Nat.zero_add]
  split
  · simp
  · simp only [oracleCalls_bind, boundedUniform_oracleCalls_zero, Nat.zero_add]
    split
    · simp
    · simp only [oracleCalls_bind, boundedUniform_oracleCalls_zero, Nat.zero_add]
      split
      · simp
      · simp only [oracleCalls_bind, selectPaired_oracleCalls_zero, Nat.zero_add]
        split
        · simp only [oracleCalls_bind, erasePaired, insertPaired, oracleCalls_many_zero,
            classifyState_oracleCalls_zero, Nat.zero_add]
          split
          · simp
          all_goals
            simp only [oracleCalls_bind, classifyState_oracleCalls_zero, Nat.zero_add]
            have hw := weightOfKind_oracleCalls_le r o₁ o₂ q w state
              (classifyState state).val
            calc
              _ ≤ 2 * n + (2 * n + 0) := by
                apply Nat.add_le_add hw
                apply Nat.add_le_add (weightOfKind_oracleCalls_le r o₁ o₂ q w _ _)
                split <;> first | exact le_of_eq (acceptance_oracleCalls_zero ..) | simp only [oracleCalls_pure_zero, Nat.le_refl]
              _ = 4 * n := by omega
        · simp

/-- INTERNAL: A capped return search has at most one chain step per attempt.
TEXLINE: main.tex:1160-1187,1333-1346 -/
theorem traceReturn_calls_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : RestartCursor n) :
    oracleCalls (traceReturn r o₁ o₂ tape s q w start) ≤ s.restartCap * (4 * n) := by
  unfold traceReturn
  calc
    _ ≤ s.restartCap * (4 * n) + 0 := by
      apply oracleCalls_bind_bound
      · unfold Arlib.Computation.Charged.repeatWhile
        apply (oracleCalls_foldlWhile_bound _ (4 * n) ?_ _ _).trans
        · simp
        intro acc index
        dsimp only
        split
        · simp
        · split
          · simp
          · simp only [oracleCalls_bind, lessThan, oracleCalls_word_zero, Nat.zero_add]
            split
            · calc
                _ ≤ 4 * n + 0 := by
                  apply oracleCalls_bind_bound
                  · exact chainStep_calls_le ..
                  · intro attempted
                    simp only [oracleCalls_bind, successor, oracleCalls_word_zero,
                      Nat.zero_add]
                    split
                    · simp
                    · simp only [oracleCalls_bind, classifyState_oracleCalls_zero,
                        Nat.zero_add]
                      split <;> simp [oracleCalls]
                _ = 4 * n := by omega
            · simp
      · intro scan
        split <;> simp
    _ = _ := by omega

/-- INTERNAL: Restarting crosses j kernels with at most τ capped returns each.
TEXLINE: main.tex:1160-1187,1333-1346 -/
theorem restartPhase_calls_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (j cursor : ℕ) :
    oracleCalls (restartPhase r o₁ o₂ tape s tables j cursor) ≤
      j * (s.τ * (s.restartCap * (4 * n))) := by
  have hfresh : oracleCalls (freshTransversal n tape cursor) = 0 := by
    unfold freshTransversal
    apply Nat.eq_zero_of_le_zero
    apply (oracleCalls_foldl_le _ 0 ?_ _ _).trans (by simp)
    intro acc i
    simp [oracleCalls, fairBit, insertPaired, successor]
  unfold restartPhase
  calc
    _ ≤ 0 + j * (s.τ * (s.restartCap * (4 * n))) := by
      apply oracleCalls_bind_bound
      · exact le_of_eq hfresh
      · intro initial
        dsimp only
        calc
          _ ≤ j * (s.τ * (s.restartCap * (4 * n))) + 0 := by
            apply oracleCalls_bind_bound
            · apply oracleCalls_repeatFor_le
              intro index current
              split
              · simp
              · simp only [oracleCalls_bind, successor, oracleCalls_word_zero,
                  ratPower_oracleCalls_zero, learnedWeightRead, oracleCalls_many_zero,
                  Nat.zero_add]
                apply oracleCalls_repeatFor_le
                intro _ current
                cases current with
                | none => simp
                | some current => exact traceReturn_calls_le ..
            · intro crossed
              cases crossed <;> simp
          _ = _ := by omega
    _ = _ := by omega

/-- INTERNAL: Each observation uses at most one exchange and one paired rank.
TEXLINE: main.tex:1333-1346 -/
theorem observePhase_calls_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (w : Multipliers n)
    (start : PairedSet n × ℕ) :
    oracleCalls (observePhase r o₁ o₂ tape s q w start) ≤ s.observations * (6 * n) := by
  unfold observePhase
  simp only [oracleCalls_bind, allocateCounts, oracleCalls_many_zero, Nat.zero_add]
  apply oracleCalls_repeatFor_le
  intro index current
  cases current with
  | none => simp
  | some current =>
      simp only [oracleCalls_bind, natEqual, oracleCalls_word_zero, Nat.zero_add]
      split
      · exact (recordObservation_oracleCalls_le ..).trans (by omega)
      · calc
          _ ≤ 4 * n + 2 * n := by
            apply oracleCalls_bind_bound
            · exact chainStep_calls_le ..
            · intro next
              cases next with
              | none => simp
              | some next => exact recordObservation_oracleCalls_le ..
          _ = _ := by omega

/-- INTERNAL: Finishing a phase only manipulates counts and rational weights. -/
theorem finishPhase_calls_zero {n : ℕ} (s : AnnealingSchedule) (j : ℕ)
    (w : Multipliers n) (observed : ObservationCursor n) :
    oracleCalls (finishPhase s j w observed) = 0 := by
  unfold finishPhase
  simp only [oracleCalls_bind, countRead, natEqual, oracleCalls_many_zero,
    oracleCalls_word_zero, Nat.zero_add]
  split
  · simp
  · simp only [oracleCalls_bind, ratOfNat, ratDiv, successor, lessThan,
      oracleCalls_many_zero, oracleCalls_word_zero, Nat.zero_add]
    apply Nat.eq_zero_of_le_zero
    change _ ≤ 0 + 0
    apply Nat.add_le_add
    · apply (oracleCalls_foldl_le _ 0 ?_ _ _).trans (by simp)
      intro current i
      apply (oracleCalls_foldl_le _ 0 ?_ _ _).trans (by simp)
      intro current k
      cases current with
      | none => simp
      | some current =>
          simp only [oracleCalls_bind, indexEqual, oracleCalls_word_zero, Nat.zero_add]
          split
          · simp
          · split
            · simp only [oracleCalls_bind,
                oracleCalls_many_zero, oracleCalls_word_zero, Nat.zero_add]
              split
              · simp
              · split
                · simp [oracleCalls, multiplierRead, ratMul, multiplierWrite]
                · simp
            · simp
    · split <;> simp

/-- INTERNAL: A finite indexed loop only needs bounds at indices below its length. -/
theorem oracleCalls_repeatFor_indexed {β : Type}
    (f : ℕ → β → Arlib.Computation.Charged Op Cell β) (N k : ℕ)
    (h : ∀ j, j < N → ∀ b, oracleCalls (f j b) ≤ k) (b : β) :
    oracleCalls (Arlib.Computation.Charged.repeatFor f N b) ≤ N * k := by
  have hfold (l : List ℕ) (hl : ∀ j ∈ l, j < N) (b : β) :
      oracleCalls (Arlib.Computation.Charged.foldl (fun b j => f j b) l b) ≤
        l.length * k := by
    induction l generalizing b with
    | nil => simp [oracleCalls]
    | cons j js ih =>
        change oracleCalls (f j b >>= _) ≤ _
        calc
          _ ≤ k + js.length * k := by
            apply oracleCalls_bind_bound
            · exact h j (hl j (by simp)) b
            · intro next
              exact ih (fun i hi => hl i (by simp [hi])) next
          _ = (j :: js).length * k := by simp [Nat.add_mul]; omega
  exact (hfold (List.range N) (by simp) b).trans
    (by simp)

/-- INTERNAL: Oracle calls of a bounded run obey a schedule-field polynomial,
independently of rational encoding lengths and output size.
TEXLINE: main.tex:1333-1346,1428-1439 -/
theorem boundedRun_oracleCalls_envelope :
    ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
      (s : AnnealingSchedule),
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      oracleCalls (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤
        100 * size ^ 100 := by
  intro n r o₁ o₂ tape s
  dsimp only
  let size := n + s.L + s.τ + s.restartCap + s.observations +
    s.drawTrials + binaryRatLength s.ρ + 1
  have hpower (a b : ℕ) : oracleCalls (natPower a b) = 0 := by
    unfold natPower
    apply Nat.eq_zero_of_le_zero
    apply (oracleCalls_repeatFor_le (k := 0) ?_ _ _).trans (by simp)
    intro _ _
    simp [natMul, oracleCalls]
  have hrun : oracleCalls (boundedRun r o₁ o₂ tape s 0) ≤
      s.L * (s.L * (s.τ * (s.restartCap * (4 * n))) + s.observations * (6 * n)) := by
    unfold boundedRun
    simp only [oracleCalls_bind, initialWeights, allocateLearnedWeights,
      oracleCalls_many_zero, Nat.zero_add]
    calc
      _ ≤ s.L * (s.L * (s.τ * (s.restartCap * (4 * n))) +
          s.observations * (6 * n)) + 0 := by
        apply Nat.add_le_add
        · apply oracleCalls_repeatFor_indexed
          intro j hj current
          cases current with
          | none => simp
          | some current =>
              simp only [oracleCalls_bind, ratPower_oracleCalls_zero, Nat.zero_add]
              apply Nat.add_le_add
              · exact (restartPhase_calls_le ..).trans
                  (Nat.mul_le_mul_right _ (Nat.le_of_lt hj))
              · split
                · simp
                · simp only [oracleCalls_bind]
                  calc
                    _ ≤ s.observations * (6 * n) + 0 := by
                      apply Nat.add_le_add
                      · exact observePhase_calls_le ..
                      · split
                        · simp
                        · simp only [oracleCalls_bind, finishPhase_calls_zero, Nat.zero_add]
                          split
                          · simp
                          · simp only [oracleCalls_bind, ratMul, successor, lessThan,
                              oracleCalls_many_zero, oracleCalls_word_zero, Nat.zero_add]
                            split <;> simp [oracleCalls, learnedWeightWrite]
                    _ = _ := by omega
        · split
          · simp
          · simp only [oracleCalls_bind, hpower, ratOfNat, ratMul,
              oracleCalls_many_zero, oracleCalls_pure_zero, Nat.zero_add, Nat.le_refl]
      _ = _ := by omega
  have hn : n ≤ size := by dsimp [size]; omega
  have hL : s.L ≤ size := by dsimp [size]; omega
  have ht : s.τ ≤ size := by dsimp [size]; omega
  have hc : s.restartCap ≤ size := by dsimp [size]; omega
  have ho : s.observations ≤ size := by dsimp [size]; omega
  have hs : 1 ≤ size := by dsimp [size]; omega
  have hpoly : s.L * (s.L * (s.τ * (s.restartCap * (4 * n))) +
      s.observations * (6 * n)) ≤ 4 * size ^ 5 + 6 * size ^ 3 := by
    calc
      _ ≤ size * (size * (size * (size * (4 * size))) + size * (6 * size)) :=
        Nat.mul_le_mul hL (Nat.add_le_add
          (Nat.mul_le_mul hL (Nat.mul_le_mul ht
            (Nat.mul_le_mul hc (Nat.mul_le_mul_left 4 hn))))
          (Nat.mul_le_mul ho (Nat.mul_le_mul_left 6 hn)))
      _ = _ := by ring
  have h5 : size ^ 5 ≤ size ^ 100 := by
    exact pow_le_pow_right₀ hs (by omega)
  have h3 : size ^ 3 ≤ size ^ 100 := by
    exact pow_le_pow_right₀ hs (by omega)
  change oracleCalls (boundedRun r o₁ o₂ tape s 0) ≤ 100 * size ^ 100
  exact hrun.trans (hpoly.trans (by omega))

end CountingMatroid.Analysis.BoundedRunOracleCalls

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · proved · closed the oracle-call envelope by uniform chain, capped-return, restart, observation, and indexed phase-loop bounds; no new proof debt.
* recovery · blocked · verified the fourteen-declaration upstream extraction in Lean; completing the planned dependency move requires edits to ResourceBound, outside assigned ownership. No new proof debt introduced.
* r15 · open · separated oracle charges from rational-size invariants; direct boundedRun simplification leaves the nested phase charge, and the reusable primitive bounds are downstream in ResourceBound.
-/
