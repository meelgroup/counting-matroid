import CountingMatroid.Analysis.PhaseChainWork

set_option autoImplicit false
namespace CountingMatroid.Analysis.FinishPhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.BoundedRunResourceEnvelope

/-- INTERNAL: A finite charged scan carries both its additive size budget and
its work, with the work priced at the largest reachable budget. -/
private theorem fold_work_size {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (D : ℕ) (C : ℕ → ℕ)
    (hmono : Monotone C)
    (hf : ∀ b i B, P b B → otherSteps (f b i) ≤ C B ∧ P (f b i).val (B + D))
    (l : List ι) (b : β) (B : ℕ) (hb : P b B) :
    otherSteps (Arlib.Computation.Charged.foldl f l b) ≤ l.length * C (B + l.length * D) ∧
      P (Arlib.Computation.Charged.foldl f l b).val (B + l.length * D) := by
  induction l generalizing b B with
  | nil => simpa [otherSteps] using hb
  | cons i l ih =>
      rw [show Arlib.Computation.Charged.foldl f (i :: l) b =
        f b i >>= fun next => Arlib.Computation.Charged.foldl f l next from rfl,
        otherSteps_bind, Arlib.Computation.Charged.val_bind]
      have hs := hf b i B hb
      have ht := ih (f b i).val (B + D) hs.2
      have he : B + D + l.length * D = B + (l.length + 1) * D := by ring
      rw [he] at ht
      simp only [List.length_cons]
      constructor
      · have hm := hmono (show B ≤ B + (l.length + 1) * D by omega)
        have hh := hs.1.trans hm
        simpa [Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hh ht.1
      · exact ht.2

/-- INTERNAL: Uniform per-entry cost of the finishing scan at multiplier size B
and count-encoding budget E. TEXLINE: main.tex:1356-1360 -/
def finishEntryBudget (n E B : ℕ) : ℕ :=
  3 * n * n + E + 10 + 4 * E ^ 2 + 2 * (B + 4 * E) ^ 2

/-- INTERNAL: The finishing routine's charge includes prefix rational divisions
and every visited multiplier, including all zero-count aborts.
TEXLINE: main.tex:1356-1378 -/
theorem finishPhase_otherSteps_le {n : ℕ} (s : AnnealingSchedule) (j B : ℕ)
    (weights : Multipliers n) (observed : ObservationCursor n)
    (hc : ∀ kind, observed.counts kind ≤ s.observations)
    (hw : ∀ i, binaryRatLength (weights i) ≤ B) :
    otherSteps (finishPhase s j weights observed) ≤
      n * n + 5 + 2 * (s.observations + 4) + 4 * (s.observations + 4) ^ 2 +
        2 * (binaryRatLength observed.numeratorSum + 3 * (s.observations + 4)) ^ 2 +
        n * n * finishEntryBudget n (s.observations + 4)
          (B + n * n * (4 * (s.observations + 4)) + n * (4 * (s.observations + 4))) := by
  let E := s.observations + 4
  let D := 4 * E
  let P : Option (Multipliers n) → ℕ → Prop :=
    fun acc B => ∀ w, acc = some w → ∀ i, binaryRatLength (w i) ≤ B
  have hcast (a : ℕ) (ha : a ≤ s.observations) : binaryRatLength (a : ℚ) ≤ E := by
    rw [binaryRatLength_natCast]
    have hl := Nat.log_le_self 2 a
    rw [← Nat.log2_eq_log_two] at hl
    dsimp [E]
    omega
  have hcastcost (a : ℕ) (ha : a ≤ s.observations) : otherSteps (ratOfNat a) ≤ E := by
    simp only [ratOfNat, work_words]
    have hl := Nat.log_le_self 2 a
    rw [← Nat.log2_eq_log_two] at hl
    dsimp [E]
    omega
  have hpzero : binaryRatLength
      ((observed.counts .transversal : ℚ) / (s.observations : ℚ)) ≤ 2 * E := by
    have := binaryRatLength_div_le (observed.counts .transversal : ℚ)
      (s.observations : ℚ)
    have := hcast _ (hc .transversal)
    have := hcast _ (le_refl _)
    omega
  have hdivcost (a b : ℚ) (K : ℕ) (h : binaryRatLength a + binaryRatLength b ≤ K) :
      otherSteps (ratDiv a b) ≤ K ^ 2 :=
    (rationalBinary_otherSteps_le .udiv a b (a / b)).trans (Nat.pow_le_pow_left h 2)
  have hmono : Monotone (finishEntryBudget n E) := by
    intro a b hab
    unfold finishEntryBudget
    gcongr
  let step : Fin n → Option (Multipliers n) → Fin n →
      Arlib.Computation.Charged Op Cell (Option (Multipliers n)) :=
    fun i current k => do
      match current with
      | none => pure none
      | some current =>
          let diagonal ← indexEqual i k
          if diagonal then pure (some current)
          else
            if h : i ≠ k then
              let count ← countRead observed.counts (.defect i k)
              let zero ← natEqual count 0
              if zero then pure none
              else if (lessThan (successor j).val s.L).val then
                let pCount ← ratOfNat count
                let pDefect ← ratDiv pCount (s.observations : ℚ)
                let old ← multiplierRead current ⟨i, k, h⟩
                let numerator ← ratMul old
                  ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
                let value ← ratDiv numerator pDefect
                let newer ← multiplierWrite current ⟨i, k, h⟩ value
                pure (some newer)
              else pure (some current)
            else pure none
  have hs : ∀ i current k K, P current K →
      otherSteps (step i current k) ≤ finishEntryBudget n E K ∧
        P (step i current k).val (K + D) := by
    intro i acc k K hb
    cases acc with
    | none => simp [step, P]
    | some current =>
        have hcurrent := hb current rfl
        dsimp only [step]
        simp only [otherSteps_bind, Arlib.Computation.Charged.val_bind]
        split
        · constructor
          · simp [indexEqual, finishEntryBudget]; omega
          · intro next hn index
            cases Option.some.inj hn
            exact (hcurrent index).trans (Nat.le_add_right _ _)
        · split
          · rename_i hik
            simp only [otherSteps_bind, Arlib.Computation.Charged.val_bind]
            split
            · constructor
              · simp [indexEqual, countRead, natEqual, finishEntryBudget]; nlinarith
              · simp [P]
            · split
              · have hpc := hcast _ (hc (.defect i k))
                have hobs := hcast _ (le_refl _)
                have hpcost := hcastcost _ (hc (.defect i k))
                have hpdef := binaryRatLength_div_le
                  (observed.counts (.defect i k) : ℚ) (s.observations : ℚ)
                have hpd : binaryRatLength
                    ((observed.counts (.defect i k) : ℚ) / (s.observations : ℚ)) ≤ 2 * E := by omega
                have hi := hcurrent ⟨i, k, hik⟩
                have hmulsize := binaryRatLength_mul_le (current ⟨i, k, hik⟩)
                  ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
                have hdivsize := binaryRatLength_div_le
                  (current ⟨i, k, hik⟩ *
                    ((observed.counts .transversal : ℚ) / (s.observations : ℚ)))
                  ((observed.counts (.defect i k) : ℚ) / (s.observations : ℚ))
                have hd₁ := hdivcost (observed.counts (.defect i k) : ℚ)
                  (s.observations : ℚ) (2 * E) (by omega)
                have hm : otherSteps (ratMul (current ⟨i, k, hik⟩)
                    ((observed.counts .transversal : ℚ) / (s.observations : ℚ))) ≤
                    (K + 4 * E) ^ 2 :=
                  (otherSteps_ratMul_le _ _).trans (Nat.pow_le_pow_left (by omega) 2)
                have hd₂ := hdivcost
                  (current ⟨i, k, hik⟩ * ((observed.counts .transversal : ℚ) / (s.observations : ℚ)))
                  ((observed.counts (.defect i k) : ℚ) / (s.observations : ℚ))
                  (K + 4 * E) (by omega)
                constructor
                · simp only [otherSteps_bind, work_pure, Nat.add_zero, indexEqual,
                    countRead, natEqual, multiplierRead, multiplierWrite,
                    ratOfNat, Arlib.Computation.Charged.val_opMany, work_word,
                    work_words, ratMul, ratDiv] at hm hd₁ hd₂ hpcost ⊢
                  unfold finishEntryBudget
                  nlinarith
                · intro next hn index
                  simp only [Arlib.Computation.Charged.val_bind, ratDiv, ratMul,
                    ratOfNat, countRead, multiplierRead, Arlib.Computation.Charged.val_opMany,
                    Arlib.Computation.Charged.val_pure, Option.some.injEq] at hn
                  subst next
                  simp only [multiplierWrite, Arlib.Computation.Charged.val_opMany]
                  split_ifs
                  · dsimp [D]
                    omega
                  · exact (hcurrent index).trans (Nat.le_add_right _ _)
              · constructor
                · simp [indexEqual, countRead, natEqual, finishEntryBudget]; nlinarith
                · intro next hn index
                  cases Option.some.inj hn
                  exact (hcurrent index).trans (Nat.le_add_right _ _)
          · constructor
            · simp [indexEqual, finishEntryBudget]; omega
            · simp [P]
  have hinner (acc : Option (Multipliers n)) (i : Fin n) (K : ℕ) (hb : P acc K) :
      otherSteps (Arlib.Computation.Charged.foldl (step i) (List.finRange n) acc) ≤
        n * finishEntryBudget n E (K + n * D) ∧
      P (Arlib.Computation.Charged.foldl (step i) (List.finRange n) acc).val (K + n * D) := by
    simpa using fold_work_size P (step i) D (finishEntryBudget n E) hmono
      (hs i) (List.finRange n) acc K hb
  have hout := fold_work_size P
    (fun acc i => Arlib.Computation.Charged.foldl (step i) (List.finRange n) acc)
    (n * D) (fun K => n * finishEntryBudget n E (K + n * D))
    (by intro a b hab; exact Nat.mul_le_mul_left n (hmono (Nat.add_le_add_right hab _)))
    hinner (List.finRange n) (some weights) B (by intro w hw'; cases Option.some.inj hw'; exact hw)
  simp only [List.length_finRange] at hout
  have houtcost : otherSteps
      (Arlib.Computation.Charged.foldl
        (fun acc i => Arlib.Computation.Charged.foldl (step i) (List.finRange n) acc)
        (List.finRange n) (some weights)) ≤
        n * n * finishEntryBudget n E (B + n * n * D + n * D) := by
    simpa only [Nat.mul_assoc] using hout.1
  have hobs := hcast _ (le_refl _)
  have hz := hcast _ (hc .transversal)
  have hcostobs := hcastcost _ (le_refl _)
  have hcostz := hcastcost _ (hc .transversal)
  have hdiv₁ := hdivcost (observed.counts .transversal : ℚ) (s.observations : ℚ)
    (2 * E) (by omega)
  have hdiv₂ := hdivcost observed.numeratorSum (s.observations : ℚ)
    (binaryRatLength observed.numeratorSum + 3 * E) (by omega)
  have hu := binaryRatLength_div_le observed.numeratorSum (s.observations : ℚ)
  have hdiv₃ := hdivcost (observed.numeratorSum / (s.observations : ℚ))
    ((observed.counts .transversal : ℚ) / (s.observations : ℚ))
    (binaryRatLength observed.numeratorSum + 3 * E) (by omega)
  have hret (ratio : ℚ) (acc : Option (Multipliers n)) :
      otherSteps (match acc with
        | none => (pure none : Arlib.Computation.Charged Op Cell (Option (ℚ × Multipliers n)))
        | some updated => pure (some (ratio, updated))) = 0 := by
    cases acc <;> simp
  unfold finishPhase
  simp only [otherSteps_bind]
  split
  · simp [countRead, natEqual]; omega
  · simp only [otherSteps_bind]
    simp only [countRead, ratOfNat, ratDiv,
      Arlib.Computation.Charged.val_opMany]
    dsimp only [step] at houtcost
    delta CountingMatroid.Program.finishPhase.match_1
      finishPhase_otherSteps_le.match_1_4 at houtcost hret ⊢
    rw [hret]
    simp only [step, countRead, natEqual, successor, lessThan,
      work_word, work_words, ratOfNat, ratDiv, Arlib.Computation.Charged.val_opMany,
      Arlib.Computation.Charged.val_op] at houtcost hcostobs hcostz hdiv₁ hdiv₂ hdiv₃ ⊢
    dsimp only [D, E] at houtcost hcostobs hcostz hdiv₁ hdiv₂ hdiv₃
    nlinarith
end CountingMatroid.Analysis.FinishPhaseWork
