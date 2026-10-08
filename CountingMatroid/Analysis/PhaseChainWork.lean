import CountingMatroid.Analysis.PhaseResourcePrimitives

set_option autoImplicit false
namespace CountingMatroid.Analysis.PhaseChainWork
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program
open CountingMatroid.Analysis.ResourceBound
open CountingMatroid.Analysis.BoundedRunResourceEnvelope
open CountingMatroid.Analysis.ScheduleOtherStepsEnvelope

/-- INTERNAL: A pure computation contributes no nonoracle work. -/
@[simp] theorem work_pure {α : Type} (x : α) :
    otherSteps (pure x : Arlib.Computation.Charged Op Cell α) = 0 := by
  simp [otherSteps]

/-- INTERNAL: One charged word instruction contributes one nonoracle step. -/
@[simp] theorem work_word {α : Type} (i : Arlib.Computation.Op) (x : α) :
    otherSteps (Arlib.Computation.Charged.op (Op.word i) x) = 1 := by
  cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.one]

/-- INTERNAL: A batch of word instructions contributes its batch length. -/
@[simp] theorem work_words {α : Type} (i : Arlib.Computation.Op) (k : ℕ) (x : α) :
    otherSteps (Arlib.Computation.Charged.opMany (Op.word i) k x) = k := by
  cases i <;> simp [otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.many]

/-- INTERNAL: A fair-bit read contributes one nonoracle step. -/
@[simp] theorem work_bit {α : Type} (x : α) :
    otherSteps (Arlib.Computation.Charged.op Op.fairBit x) = 1 := by
  simp [otherSteps, Arlib.Computation.Op.all, Arlib.Computation.CostVec.one]

/-- INTERNAL: Original-oracle charges are excluded from the nonoracle tally. -/
@[simp] theorem work_oracle {n : ℕ} (which : Bool) (o : IndependenceOracle n)
    (q : Query n) : otherSteps (oracleQuery which o q) = 0 := by
  cases which <;> simp [oracleQuery, otherSteps, Arlib.Computation.Op.all,
    Arlib.Computation.CostVec.one]

/-- INTERNAL: Mapping a pure result preserves the charged work. -/
@[simp] theorem work_map {α β : Type} (f : α → β)
    (p : Arlib.Computation.Charged Op Cell α) : otherSteps (f <$> p) = otherSteps p := by
  simp only [otherSteps, Arlib.Computation.Charged.cost_map]

/-- INTERNAL: Hard-capped rejection sampling has a uniform bound independent
of the tape and cursor. TEXLINE: main.tex:1392-1421 -/
theorem boundedUniform_otherSteps_le (tape : ℕ → Bool) (trials v cursor : ℕ) :
    otherSteps (boundedUniform tape trials v cursor) ≤
      3 + trials * (3 * (v.log2 + 1) + 2) := by
  have hwidth : (v - 1).log2 + 1 ≤ v.log2 + 1 := by
    simp only [Nat.log2_eq_log_two]
    exact Nat.add_le_add_right (Nat.log_mono_right (Nat.sub_le v 1)) 1
  have hinner (width cursor : ℕ) (acc : ℕ × ℕ) :
      otherSteps (Arlib.Computation.Charged.repeatFor (fun _ inner => do
        let bit ← fairBit tape inner.2
        let value ← appendBit inner.1 bit
        let next ← successor inner.2
        pure (value, next)) width acc) ≤ width * 3 := by
    unfold Arlib.Computation.Charged.repeatFor
    apply (otherSteps_foldl_le_of_mem _ _ 3 ?_ acc).trans_eq (by simp)
    intro b a ha
    simp [otherSteps_bind, fairBit, appendBit, successor]
  unfold boundedUniform
  simp only [otherSteps_bind]
  split
  · simp [lessThan]; omega
  · simp only [otherSteps_bind]
    split
    · simp [lessThan]; omega
    · simp only [otherSteps_bind]
      have hout := otherSteps_foldl_le_of_mem
        (fun (acc : Option ℕ × ℕ) (_ : ℕ) => do
          let done ← isSome acc.1
          if done then pure acc
          else
            let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
              let bit ← fairBit tape inner.2
              let value ← appendBit inner.1 bit
              let next ← successor inner.2
              pure (value, next)) (uniformWidth v).val (0, acc.2)
            let accepted ← lessThan trial.1 v
            if accepted then pure (some trial.1, trial.2)
            else pure (none, trial.2)) (List.range trials)
        (3 * (v.log2 + 1) + 2) ?_ (none, cursor)
      · simpa only [lessThan, uniformWidth, work_word,
          Arlib.Computation.Charged.val_op, List.length_range,
          Arlib.Computation.Charged.repeatFor, ← Nat.add_assoc] using Nat.add_le_add_left hout 3
      · intro acc a ha
        simp only [otherSteps_bind]
        split
        · simp [isSome]
        · have hi := hinner (uniformWidth v).val acc.2 (0, acc.2)
          simp only [otherSteps_bind]
          split <;> simp only [work_pure, Nat.add_zero]
          all_goals simp only [isSome, lessThan, work_word] at *
          all_goals simp only [uniformWidth, Arlib.Computation.Charged.val_op] at hi ⊢
          all_goals nlinarith
/-- INTERNAL: Query construction in a greedy rank scan has cubic nonoracle work.
TEXLINE: main.tex:1333-1346 -/
theorem greedyRank_otherSteps_le {n : ℕ} (which : Bool)
    (o : IndependenceOracle n) (target : Finset (Fin n)) :
    otherSteps (greedyRank which o target) ≤ n * (n * (n + 1) + n + 3) := by
  unfold greedyRank
  simp only [otherSteps_bind, work_pure, Nat.add_zero]
  apply (otherSteps_foldl_le_of_mem _ _ (n * (n + 1) + n + 3) ?_ _).trans_eq
    (by simp)
  intro acc i hi
  simp only [otherSteps_bind]
  split
  · simp only [otherSteps_bind]
    split <;> simp [containsElement, insertElement, encodeQuery, successor,
      otherSteps_bind] <;> omega
  · simp [containsElement]; omega

/-- INTERNAL: Projecting a paired state costs linear scan work times membership
cost. TEXLINE: main.tex:1333-1346 -/
theorem pairedProjections_otherSteps_le {n : ℕ} (state : PairedSet n) :
    otherSteps (pairedProjections state) ≤ n * (4 * n + 4) := by
  unfold pairedProjections
  apply (otherSteps_foldl_le_of_mem _ _ (4 * n + 4) ?_ _).trans_eq (by simp)
  intro acc i hi
  simp only [otherSteps_bind]
  split <;> simp only [otherSteps_bind]
  all_goals split <;> simp [otherSteps_bind, containsPaired, insertElement, successor]
  all_goals omega

/-- INTERNAL: The paired-rank evaluation uses two bounded greedy scans and
bounded projection work. TEXLINE: main.tex:1333-1346 -/
theorem pairedRank_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (state : PairedSet n) : otherSteps (pairedRank r o₁ o₂ state) ≤ 8 * (n + 1) ^ 3 := by
  unfold pairedRank
  simp only [otherSteps_bind, work_map]
  have hp := pairedProjections_otherSteps_le state
  have h₁ := greedyRank_otherSteps_le false o₁ (pairedProjections state).val.1
  have h₂ := greedyRank_otherSteps_le true o₂ (pairedProjections state).val.2.1
  simp only [natAdd, natSub, work_word]
  nlinarith [sq_nonneg (n : ℤ)]

/-- INTERNAL: Classifying a state is bounded for all occupancy patterns.
TEXLINE: main.tex:1333-1346 -/
theorem classifyState_otherSteps_le {n : ℕ} (state : PairedSet n) :
    otherSteps (classifyState state) ≤ n * (4 * n + 3) + 1 := by
  unfold classifyState
  rw [otherSteps_bind]
  have hs := otherSteps_foldl_le_of_mem
    (fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) => do
      let x ← containsPaired state (i, false)
      let y ← containsPaired state (i, true)
      if x then
        if y then
          let seen ← isSome acc.2.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (acc.1, some i, acc.2.2)
        else pure acc
      else
        if y then pure acc
        else
          let seen ← isSome acc.1
          if seen then pure (acc.1, acc.2.1, true)
          else pure (some i, acc.2.1, acc.2.2))
    (List.finRange n) (4 * n + 3) ?_ (none, none, false)
  · simp only [List.length_finRange] at hs
    split
    · simp only [work_pure]; omega
    · split <;> try simp only [work_pure]
      all_goals try omega
      simp only [otherSteps_bind]
      split <;> simp [indexEqual] <;> omega
  · intro acc i hi
    simp only [otherSteps_bind]
    split <;> split
    all_goals try simp only [otherSteps_bind]
    all_goals try split
    all_goals simp [containsPaired, isSome] <;> omega

/-- INTERNAL: Selecting a paired label costs at most one two-element scan per
original ground element. TEXLINE: main.tex:1333-1346 -/
theorem selectPaired_otherSteps_le {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) :
    otherSteps (selectPaired state occupied k) ≤ 2 * n * (2 * n + 3) := by
  have hs (acc : Option (PairedGround n) × ℕ) (e : PairedGround n) :
      otherSteps (selectionVisit state occupied k acc e) ≤ 2 * n + 3 := by
    unfold selectionVisit
    simp only [otherSteps_bind]
    split <;> split
    all_goals try simp only [otherSteps_bind]
    all_goals try split
    all_goals simp [containsPaired, natEqual, successor, otherSteps_bind] <;> omega
  unfold selectPaired
  simp only [otherSteps_bind, work_pure, Nat.add_zero]
  have hout := otherSteps_foldl_le_of_mem
    (fun (acc : Option (PairedGround n) × ℕ) (i : Fin n) =>
      Arlib.Computation.Charged.foldl (selectionVisit state occupied k)
        [((i, false) : PairedGround n), (i, true)] acc)
    (List.finRange n) (2 * (2 * n + 3)) ?_ (none, 0)
  · simpa [Nat.mul_assoc, Nat.mul_comm, Nat.mul_left_comm] using hout
  · intro acc i hi
    simpa using otherSteps_foldl_le_of_mem (selectionVisit state occupied k)
      [((i, false) : PairedGround n), (i, true)] (2 * n + 3)
      (fun b a ha => hs b a) acc

/-- INTERNAL: State weights have bounded size and work for arbitrary oracle
answers and bounded input multipliers. TEXLINE: main.tex:1384-1390 -/
theorem weightOfKind_work_size {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (state : PairedSet n) (kind : StateKind n)
    (K : ℕ) (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (weightOfKind r o₁ o₂ q weights state kind) ≤
      8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2 ∧
    (∀ w, (weightOfKind r o₁ o₂ q weights state kind).val = some w →
      binaryRatLength w ≤ 2 * K) := by
  have hd : (natSub n (pairedRank r o₁ o₂ state).val).val ≤ n := Nat.sub_le _ _
  have hl : binaryRatLength
      (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val ≤ K := by
    have hp := ratPower_binary_length_le q (natSub n (pairedRank r o₁ o₂ state).val).val
    have hm := Nat.mul_le_mul_right (binaryRatLength q) hd
    omega
  have hc : otherSteps
      (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val) ≤ n * K ^ 2 := by
    apply (ratPower_otherSteps_le q _).trans
    exact Nat.mul_le_mul hd (Nat.pow_le_pow_left (by
      have hm := Nat.mul_le_mul_right (binaryRatLength q) hd
      omega) 2)
  have hr := pairedRank_otherSteps_le r o₁ o₂ state
  cases kind with
  | invalid => simp [weightOfKind]
  | transversal =>
      constructor
      · simp only [weightOfKind, otherSteps_bind, work_map, natSub, work_word, work_pure]
        simp only [natSub, Arlib.Computation.Charged.val_op] at hc ⊢
        nlinarith
      · intro w he
        simp only [weightOfKind, Arlib.Computation.Charged.val_bind,
          Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
        subst w
        exact hl.trans (by omega)
  | defect i k =>
      by_cases hik : i ≠ k
      · have hm := otherSteps_ratMul_le (weights ⟨i, k, hik⟩)
          (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val
        have hml := binaryRatLength_mul_le (weights ⟨i, k, hik⟩)
          (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val
        have hi := hw ⟨i, k, hik⟩
        have hmc : otherSteps (ratMul (weights ⟨i, k, hik⟩)
            (ratPower q (natSub n (pairedRank r o₁ o₂ state).val).val).val) ≤
            4 * K ^ 2 := by
          apply hm.trans
          calc
            _ ≤ (2 * K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
            _ = _ := by ring
        constructor
        · simp only [weightOfKind, dif_pos hik, otherSteps_bind, work_map,
            multiplierRead, Arlib.Computation.Charged.val_opMany, work_words,
            natSub, work_word, work_pure]
          simp only [natSub, Arlib.Computation.Charged.val_op] at hc hmc ⊢
          nlinarith
        · intro w he
          simp only [weightOfKind, dif_pos hik, Arlib.Computation.Charged.val_bind,
            ratMul, multiplierRead, Arlib.Computation.Charged.val_opMany,
            Arlib.Computation.Charged.val_pure, Option.some.injEq] at he
          subst w
          omega
      · simp [weightOfKind, hik]

/-- INTERNAL: Explicit sum of the worst branch costs of a capped chain step.
TEXLINE: main.tex:1333-1421 -/
def chainBudget (n trials K : ℕ) : ℕ :=
  2 + 3 * (3 + trials * (3 * (4 * K + n + 1) + 2)) +
    2 * (2 * n * (2 * n + 3)) + 2 * (2 * n + 1) +
    2 * (n * (4 * n + 3) + 1) +
    2 * (8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2) +
    16 * K ^ 2 + 12 * K + 5

/-- INTERNAL: Each capped Metropolis step has polynomial nonoracle work, even
when an exchange is invalid or any rejection draw aborts.
TEXLINE: main.tex:1333-1346,1384-1421 -/
theorem chainStep_otherSteps_le {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor K : ℕ)
    (hq : binaryRatLength 1 + n * binaryRatLength q ≤ K)
    (hw : ∀ i, binaryRatLength (weights i) ≤ K) :
    otherSteps (chainStep r o₁ o₂ tape trials q weights state cursor) ≤
      chainBudget n trials K := by
  unfold chainBudget
  have hK : 4 ≤ K := by
    have hone : binaryRatLength (1 : ℚ) = 4 := by decide
    omega
  have hlog : n.log2 ≤ n := by
    simpa only [Nat.log2_eq_log_two] using Nat.log_le_self 2 n
  have hdraw (v c : ℕ) (hv : v.log2 ≤ 4 * K + n) :
      otherSteps (boundedUniform tape trials v c) ≤
        3 + trials * (3 * (4 * K + n + 1) + 2) := by
    exact (boundedUniform_otherSteps_le tape trials v c).trans
      (Nat.add_le_add_left (Nat.mul_le_mul_left trials (by omega)) 3)
  have hsel (occupied : Bool) (k : ℕ) := selectPaired_otherSteps_le state occupied k
  have hkind (x : PairedSet n) := classifyState_otherSteps_le x
  have hweight (x : PairedSet n) (kind : StateKind n) :=
    weightOfKind_work_size r o₁ o₂ q weights x kind K hq hw
  have haccept (old new : ℚ) (x y : PairedSet n) (c : ℕ)
      (ho : binaryRatLength old ≤ 2 * K) (hn : binaryRatLength new ≤ 2 * K) :
      otherSteps (do
        let ratio ← ratDiv new old
        let needsDraw ← ratLess ratio 1
        if needsDraw then
          let denominator ← rationalDenominator ratio
          let numerator ← rationalNumerator ratio
          let acceptedDraw ← boundedUniform tape trials denominator c
          match acceptedDraw.1 with
          | none => pure none
          | some value =>
              let accepted ← lessThan value numerator
              if accepted then pure (some (y, acceptedDraw.2))
              else pure (some (x, acceptedDraw.2))
        else pure (some (y, c))) ≤
        16 * K ^ 2 + 12 * K + 5 +
          (3 + trials * (3 * (4 * K + n + 1) + 2)) := by
    have hr : binaryRatLength (ratDiv new old).val ≤ 4 * K := by
      have := binaryRatLength_div_le new old
      simpa only [ratDiv, Arlib.Computation.Charged.val_opMany] using
        (this.trans (by omega))
    have hdiv : otherSteps (ratDiv new old) ≤ 16 * K ^ 2 := by
      have hb := rationalBinary_otherSteps_le .udiv new old (new / old)
      apply hb.trans
      calc
        _ ≤ (4 * K) ^ 2 := Nat.pow_le_pow_left (by omega) 2
        _ = _ := by ring
    have hless := ratLess_otherSteps_le (ratDiv new old).val 1
    have hden : otherSteps (rationalDenominator (ratDiv new old).val) ≤ 4 * K := by
      simp only [rationalDenominator, work_words]
      change (ratDiv new old).val.num.natAbs.log2 +
        (ratDiv new old).val.den.log2 + 3 ≤ 4 * K
      unfold binaryRatLength binaryNatLength at hr
      omega
    have hnum : otherSteps (rationalNumerator (ratDiv new old).val) ≤ 4 * K := by
      simp only [rationalNumerator, work_words]
      change (ratDiv new old).val.num.natAbs.log2 +
        (ratDiv new old).val.den.log2 + 3 ≤ 4 * K
      unfold binaryRatLength binaryNatLength at hr
      omega
    have hd := hdraw (rationalDenominator (ratDiv new old).val).val c (by
      simp only [rationalDenominator, Arlib.Computation.Charged.val_opMany]
      unfold binaryRatLength binaryNatLength at hr
      omega)
    simp only [otherSteps_bind]
    split
    · simp only [otherSteps_bind]
      split
      · simp only [work_pure, Nat.add_zero]
        have hone : binaryRatLength (1 : ℚ) = 4 := by decide
        omega
      · simp only [otherSteps_bind]
        split <;> simp only [lessThan, work_word, work_pure, Nat.add_zero]
        all_goals have hone : binaryRatLength (1 : ℚ) = 4 := by decide
        all_goals omega
    · simp only [work_pure, Nat.add_zero]
      have hone : binaryRatLength (1 : ℚ) = 4 := by decide
      omega
  have hpairs (x y : PairedSet n) (kx ky : StateKind n) (c : ℕ) :
      otherSteps (do
        let oldWeight ← weightOfKind r o₁ o₂ q weights x kx
        let newWeight ← weightOfKind r o₁ o₂ q weights y ky
        match oldWeight, newWeight with
        | some oldWeight, some newWeight => do
            let ratio ← ratDiv newWeight oldWeight
            let needsDraw ← ratLess ratio 1
            if needsDraw then
              let denominator ← rationalDenominator ratio
              let numerator ← rationalNumerator ratio
              let acceptedDraw ← boundedUniform tape trials denominator c
              match acceptedDraw.1 with
              | none => pure none
              | some value =>
                  let accepted ← lessThan value numerator
                  if accepted then pure (some (y, acceptedDraw.2))
                  else pure (some (x, acceptedDraw.2))
            else pure (some (y, c))
        | _, _ => pure none) ≤
        2 * (8 * (n + 1) ^ 3 + (n + 4) * K ^ 2 + n * n + 2) +
        16 * K ^ 2 + 12 * K + 5 +
          (3 + trials * (3 * (4 * K + n + 1) + 2)) := by
    have hx := hweight x kx
    have hy := hweight y ky
    simp only [otherSteps_bind]
    split
    · rename_i old new ho hn
      have ha := haccept old new x y c (hx.2 old ho) (hy.2 new hn)
      omega
    · simp only [work_pure]
      omega
  unfold chainStep
  simp only [otherSteps_bind]
  split
  · simp [fairBit, successor]
  · have hd₁ := hdraw n (successor cursor).val (by omega)
    simp only [otherSteps_bind]
    split
    · simp only [work_pure, Nat.add_zero, fairBit, successor, work_word, work_bit,
        Arlib.Computation.Charged.val_op] at hd₁ ⊢
      omega
    · rename_i aIndex haIndex
      have hd₂ := hdraw n (boundedUniform tape trials n (successor cursor).val).val.2
        (by omega)
      simp only [otherSteps_bind]
      split
      · simp only [work_pure, Nat.add_zero, fairBit, successor, work_word, work_bit,
          Arlib.Computation.Charged.val_op] at hd₁ hd₂ ⊢
        omega
      · rename_i bIndex hbIndex
        have hs₁ := hsel true aIndex
        have hs₂ := hsel false bIndex
        simp only [otherSteps_bind]
        split
        · rename_i a b ha hb
          have hk := hkind (insertPaired (erasePaired state a).val b).val
          simp only [otherSteps_bind]
          split
          · simp only [work_pure, Nat.add_zero, fairBit, successor, erasePaired,
              insertPaired, work_word, work_words, work_bit,
              Arlib.Computation.Charged.val_op] at hd₁ hd₂ hs₁ hs₂ hk ⊢
            omega
          · have hkold := hkind state
            have hp := hpairs state (insertPaired (erasePaired state a).val b).val
              (classifyState state).val
              (classifyState (insertPaired (erasePaired state a).val b).val).val
              (boundedUniform tape trials n
                (boundedUniform tape trials n (successor cursor).val).val.2).val.2
            rw [otherSteps_bind] 
            simp only [fairBit, successor, erasePaired, insertPaired,
              work_word, work_words, work_bit, Arlib.Computation.Charged.val_op,
              Arlib.Computation.Charged.val_opMany] at hd₁ hd₂ hs₁ hs₂ hk hp ⊢
            delta CountingMatroid.Program.chainStep.match_3
              CountingMatroid.Program.chainStep.match_1
              chainStep_otherSteps_le.match_1_15 chainStep_otherSteps_le.match_1_3
              chainStep_otherSteps_le._sparseCasesOn_1_15
              CountingMatroid.Program.classifyState._sparseCasesOn_2 at hp ⊢
            omega
        · simp only [work_pure, Nat.add_zero, fairBit, successor, work_word, work_bit,
            Arlib.Computation.Charged.val_op] at hd₁ hd₂ hs₁ hs₂ ⊢
          omega
end CountingMatroid.Analysis.PhaseChainWork
