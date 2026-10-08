import CountingMatroid.Analysis.PhaseChainWork

set_option autoImplicit false
namespace CountingMatroid.Analysis.ObservePhaseWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope
open CountingMatroid.Analysis.RationalHeight

/-- INTERNAL: An observation's branch costs, including the height-bounded
rational accumulator addition. TEXLINE: main.tex:1362-1378 -/
def recordBudget (n R H : ℕ) : ℕ :=
  n * (4 * n + 3) + 1 + 3 * (n * n + 2) + 8 * (n + 1) ^ 3 + 1 +
    n * (4 + n * R) ^ 2 + (2 * H + 2 + (4 + n * R)) ^ 2

/-- INTERNAL: Recording an observation has bounded charge when the current
accumulator has bounded height. TEXLINE: main.tex:1362-1378 -/
theorem recordObservation_otherSteps_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ) (current : ObservationCursor n)
    (H : ℕ) (hh : rationalHeight current.numeratorSum ≤ H) :
    otherSteps (recordObservation r o₁ o₂ rho current) ≤
      recordBudget n (binaryRatLength rho) H := by
  have hone : binaryRatLength (1 : ℚ) = 4 := by decide
  have hl := ratPower_binary_length_le rho
    (natSub n (pairedRank r o₁ o₂ current.state).val).val
  have hm := Nat.mul_le_mul_right (binaryRatLength rho)
    (Nat.sub_le n (pairedRank r o₁ o₂ current.state).val)
  have hs := binaryRatLength_le_height current.numeratorSum
  have hp : otherSteps (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val) ≤
      n * (4 + n * binaryRatLength rho) ^ 2 := by
    apply (ratPower_otherSteps_le rho _).trans
    apply Nat.mul_le_mul (Nat.sub_le _ _) (Nat.pow_le_pow_left _ 2)
    simpa only [hone, natSub, Arlib.Computation.Charged.val_op] using Nat.add_le_add_left hm (binaryRatLength 1)
  have ha := rationalBinary_otherSteps_le .add current.numeratorSum
    (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val).val
    (current.numeratorSum +
      (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val).val)
  have ha' : otherSteps (ratAdd current.numeratorSum
      (ratPower rho (natSub n (pairedRank r o₁ o₂ current.state).val).val).val) ≤
      (2 * H + 2 + (4 + n * binaryRatLength rho)) ^ 2 := by
    apply ha.trans
    apply Nat.pow_le_pow_left _ 2
    simp only [natSub, Arlib.Computation.Charged.val_op] at hl ⊢
    omega
  have hr := pairedRank_otherSteps_le r o₁ o₂ current.state
  have hc := classifyState_otherSteps_le current.state
  unfold recordObservation recordBudget
  rw [otherSteps_bind]
  split
  · simp; omega
  · simp [otherSteps_bind, countIncrement]; omega
  · simp only [otherSteps_bind, work_pure, Nat.add_zero, countIncrement, work_words,
      natSub, work_word, Arlib.Computation.Charged.val_op]
    simp only [natSub, Arlib.Computation.Charged.val_op] at hp ha'
    omega

/-- INTERNAL: Carry a growing size invariant through a finite charged loop,
charging a fixed budget only at states reached before the loop cap. -/
private theorem fold_work_growth {ι β : Type} (P : β → ℕ → Prop)
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (N B : ℕ)
    (hf : ∀ b i k, k < N → P b k →
      otherSteps (f b i) ≤ B ∧ P (f b i).val (k + 1))
    (l : List ι) (b : β) (k : ℕ) (hk : k + l.length ≤ N) (hb : P b k) :
    otherSteps (Arlib.Computation.Charged.foldl f l b) ≤ l.length * B := by
  induction l generalizing b k with
  | nil => simp [otherSteps]
  | cons i l ih =>
      rw [show Arlib.Computation.Charged.foldl f (i :: l) b =
        f b i >>= fun next => Arlib.Computation.Charged.foldl f l next from rfl,
        otherSteps_bind]
      have hs := hf b i k (by simp only [List.length_cons] at hk; omega) hb
      have ht := ih (f b i).val (k + 1) (by simp only [List.length_cons] at hk; omega) hs.2
      simpa [List.length_cons, Nat.succ_mul, Nat.add_comm] using Nat.add_le_add hs.1 ht

/-- INTERNAL: The observation loop's work is bounded using the reached
accumulator-height invariant, rather than a bound for arbitrary fold inputs.
TEXLINE: main.tex:1362-1378,1428-1439 -/
theorem observePhase_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (q : ℚ) (weights : Multipliers n)
    (start : PairedSet n × ℕ) (K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (observePhase r o₁ o₂ tape s q weights start) ≤
      n * n + 1 + s.observations *
        (1 + chainBudget n s.drawTrials K +
          recordBudget n (binaryRatLength s.ρ)
            (1 + s.observations * (4 + n * binaryRatLength s.ρ + 1))) := by
  let D := 4 + n * binaryRatLength s.ρ + 1
  let P : Option (ObservationCursor n) → ℕ → Prop :=
    fun acc k => ∀ next, acc = some next → rationalHeight next.numeratorSum ≤ 1 + k * D
  unfold observePhase
  rw [otherSteps_bind]
  simp only [allocateCounts, work_words]
  apply Nat.add_le_add_left
  unfold Arlib.Computation.Charged.repeatFor
  apply (fold_work_growth P _ s.observations
    (1 + chainBudget n s.drawTrials K +
      recordBudget n (binaryRatLength s.ρ) (1 + s.observations * D)) ?_
    (List.range s.observations) _ 0 (by simp) ?_).trans_eq (by simp [D])
  · intro acc index k hk hacc
    dsimp only
    cases acc with
    | none => simp [P]
    | some current =>
        have hcur := hacc current rfl
        have hg : rationalHeight current.numeratorSum ≤ 1 + s.observations * D := by
          have := Nat.mul_le_mul_right D (Nat.le_of_lt hk)
          omega
        have hrec := recordObservation_otherSteps_le r o₁ o₂ s.ρ current _ hg
        have hc := chainStep_otherSteps_le r o₁ o₂ tape s.drawTrials q weights
          current.state current.bitCursor K hq hw
        simp only [otherSteps_bind, Arlib.Computation.Charged.val_bind]
        split
        · constructor
          · simp [natEqual]; omega
          · intro next hn
            have hh := recordObservation_height_le r o₁ o₂ s.ρ current next hn
            have hone : binaryRatLength (1 : ℚ) = 4 := by decide
            dsimp [P, D] at *
            nlinarith
        · simp only [otherSteps_bind, Arlib.Computation.Charged.val_bind]
          split
          · constructor
            · simp [natEqual]; omega
            · simp [P]
          · rename_i state cursor he
            have hnrec := recordObservation_otherSteps_le r o₁ o₂ s.ρ
              ⟨state, cursor, current.counts, current.numeratorSum⟩ _ hg
            constructor
            · simp [natEqual]; omega
            · intro next hn
              have hh := recordObservation_height_le r o₁ o₂ s.ρ
                ⟨state, cursor, current.counts, current.numeratorSum⟩ next hn
              have hone : binaryRatLength (1 : ℚ) = 4 := by decide
              dsimp [P, D] at *
              nlinarith
  · intro next hn
    cases Option.some.inj hn
    norm_num [rationalHeight, Nat.log2_eq_log_two]
end CountingMatroid.Analysis.ObservePhaseWork
