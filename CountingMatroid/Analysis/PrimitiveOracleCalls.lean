import CountingMatroid.Model.Program

set_option autoImplicit false

namespace CountingMatroid.Analysis.ResourceBound

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Model.Operations

/-- INTERNAL: Oracle charges add when charged computations are sequenced. -/
theorem oracleCalls_bind {α β : Type}
    (p : Arlib.Computation.Charged Op Cell α)
    (f : α → Arlib.Computation.Charged Op Cell β) :
    oracleCalls (p >>= f) = oracleCalls p + oracleCalls (f p.val) := by
  simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]

/-- INTERNAL: A uniform per-iteration oracle bound controls a charged loop. -/
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

/-- INTERNAL: A uniform per-element oracle bound controls a charged list scan. -/
theorem oracleCalls_foldl_le {β ι : Type}
    (f : β → ι → Arlib.Computation.Charged Op Cell β) (k : ℕ)
    (h : ∀ b a, oracleCalls (f b a) ≤ k) :
    ∀ l b, oracleCalls (Arlib.Computation.Charged.foldl f l b) ≤ l.length * k := by
  intro l
  induction l with
  | nil => intro b; simp [oracleCalls]
  | cons a l ih =>
      intro b
      have ha := h b a
      have hr := ih (f b a).val
      simp only [List.length_cons]
      have hs : oracleCalls (Arlib.Computation.Charged.foldl f (a :: l) b) =
          oracleCalls (f b a) +
            oracleCalls (Arlib.Computation.Charged.foldl f l (f b a).val) := by
        simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]
      rw [hs]
      calc
        oracleCalls (f b a) + oracleCalls (Arlib.Computation.Charged.foldl f l (f b a).val)
            ≤ k + l.length * k := Nat.add_le_add ha hr
        _ = (l.length + 1) * k := by ring

/-- INTERNAL: A greedy rank scan asks the supplied independence oracle at most
once per ground element.
TEXLINE: main.tex:1333-1346 -/
theorem greedyRank_oracleCalls_le {n : ℕ} (which : Bool)
    (oracle : IndependenceOracle n) (target : Finset (Fin n)) :
    oracleCalls (greedyRank which oracle target) ≤ n := by
  unfold greedyRank
  have hstep : ∀ (acc : Finset (Fin n) × ℕ) (i : Fin n),
      oracleCalls (do
        let present ← containsElement target i
        if present then
          let candidate ← insertElement acc.1 i
          let q ← encodeQuery candidate
          let independent ← oracleQuery which oracle q
          if independent then
            let size ← successor acc.2
            pure (candidate, size)
          else pure acc
        else pure acc) ≤ 1 := by
    intro acc i
    by_cases hi : i ∈ target
    · cases which <;>
        simp [containsElement, insertElement, encodeQuery, oracleQuery,
          successor, oracleCalls, hi] <;>
        split_ifs <;> simp_all
    · simp [containsElement, insertElement, encodeQuery, oracleQuery,
        successor, oracleCalls, hi]
  simpa [oracleCalls] using
    oracleCalls_foldl_le _ 1 hstep (List.finRange n)
      ((∅ : Finset (Fin n)), 0)

/-- INTERNAL: The paired-state projection scan makes no independence queries. -/
theorem pairedProjections_oracleCalls_zero {n : ℕ} (state : PairedSet n) :
    oracleCalls (pairedProjections state) = 0 := by
  unfold pairedProjections
  have hstep : ∀ (acc : Finset (Fin n) × Finset (Fin n) × ℕ) (i : Fin n),
      oracleCalls (do
        let inX ← containsPaired state (i, false)
        let x ← if inX then insertElement acc.1 i else pure acc.1
        let inY ← containsPaired state (i, true)
        if inY then
          let ysize ← successor acc.2.2
          pure (x, acc.2.1, ysize)
        else
          let complementY ← insertElement acc.2.1 i
          pure (x, complementY, acc.2.2)) ≤ 0 := by
    intro acc i
    by_cases hx : (i, false) ∈ state <;>
      by_cases hy : (i, true) ∈ state <;>
      simp [containsPaired, insertElement, successor, oracleCalls, hx, hy]
  have h := oracleCalls_foldl_le _ 0 hstep (List.finRange n)
    ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)
  simpa [oracleCalls] using Nat.eq_zero_of_le_zero h

/-- INTERNAL: The paired-rank formula makes at most two greedy scans.
TEXLINE: main.tex:1333-1346 -/
theorem pairedRank_oracleCalls_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (state : PairedSet n) :
    oracleCalls (pairedRank r o₁ o₂ state) ≤ 2 * n := by
  unfold pairedRank
  simp only [oracleCalls_bind]
  rw [pairedProjections_oracleCalls_zero]
  simp only [Nat.zero_add]
  have h₁ := greedyRank_oracleCalls_le false o₁ (pairedProjections state).val.1
  have h₂ := greedyRank_oracleCalls_le true o₂ (pairedProjections state).val.2.1
  simp [natAdd, natSub, oracleCalls] at *
  calc
    _ ≤ n + n := Nat.add_le_add h₁ h₂
    _ = 2 * n := by ring

/-- INTERNAL: Forming a rational power performs no independence queries. -/
theorem ratPower_oracleCalls_zero (q : ℚ) (exponent : ℕ) :
    oracleCalls (CountingMatroid.Program.ratPower q exponent) = 0 := by
  have h := oracleCalls_repeatFor_le (k := 0)
    (f := fun _ acc => ratMul acc q)
    (by intro _ _; simp [ratMul, oracleCalls]) exponent 1
  simpa [CountingMatroid.Program.ratPower] using Nat.eq_zero_of_le_zero h

/-- INTERNAL: Evaluating one paired-state weight uses at most one paired rank.
TEXLINE: main.tex:1380-1390 -/
theorem weightOfKind_oracleCalls_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (kind : StateKind n) :
    oracleCalls (CountingMatroid.Program.weightOfKind r o₁ o₂ q weights state kind) ≤
      2 * n := by
  cases kind with
  | invalid => simp [CountingMatroid.Program.weightOfKind, oracleCalls]
  | transversal =>
      have hp := ratPower_oracleCalls_zero q
        (n - (pairedRank r o₁ o₂ state).val)
      have hr := pairedRank_oracleCalls_le r o₁ o₂ state
      simp [CountingMatroid.Program.weightOfKind,
        natSub, oracleCalls] at hp hr ⊢
      omega
  | defect i j =>
      by_cases hij : i ≠ j
      · have hp := ratPower_oracleCalls_zero q
          (n - (pairedRank r o₁ o₂ state).val)
        have hr := pairedRank_oracleCalls_le r o₁ o₂ state
        simp [CountingMatroid.Program.weightOfKind, hij,
          natSub, multiplierRead, ratMul, oracleCalls] at hp hr ⊢
        omega
      · simp [CountingMatroid.Program.weightOfKind, hij, oracleCalls]

/-- INTERNAL: Classifying a paired state does not query either oracle.
TEXLINE: main.tex:1333-1346 -/
theorem classifyState_oracleCalls_zero {n : ℕ} (state : PairedSet n) :
    oracleCalls (CountingMatroid.Program.classifyState state) = 0 := by
  unfold CountingMatroid.Program.classifyState
  have hstep : ∀ (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n),
      oracleCalls (do
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
            else pure (some i, acc.2.1, acc.2.2)) ≤ 0 := by
    intro acc i
    rcases acc with ⟨a, b, c⟩
    cases a <;> cases b <;>
      by_cases hx : (i, false) ∈ state <;>
      by_cases hy : (i, true) ∈ state <;>
      simp [containsPaired, isSome, oracleCalls, hx, hy]
  have h := oracleCalls_foldl_le _ 0 hstep (List.finRange n)
    ((none : Option (Fin n)), (none : Option (Fin n)), false)
  have hz : oracleCalls (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (Fin n)), (none : Option (Fin n)), false)) = 0 :=
    Nat.eq_zero_of_le_zero (by simpa using h)
  simp only [oracleCalls_bind]
  rw [hz]
  simp only [Nat.zero_add]
  split_ifs
  · simp [oracleCalls]
  · rename_i hnot
    cases h₁ : (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (Fin n)), (none : Option (Fin n)), false)).val.1 <;>
    cases h₂ : (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (Fin n)), (none : Option (Fin n)), false)).val.2.1 <;>
    simp [indexEqual, oracleCalls]
    case neg.some.some x y =>
      by_cases hxy : x = y <;> simp [hxy]

/-- INTERNAL: Recording an observation performs at most one paired-rank scan.
TEXLINE: main.tex:1333-1346 -/
theorem recordObservation_oracleCalls_le {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (rho : ℚ)
    (current : CountingMatroid.Program.ObservationCursor n) :
    oracleCalls (CountingMatroid.Program.recordObservation r o₁ o₂ rho current) ≤
      2 * n := by
  unfold CountingMatroid.Program.recordObservation
  simp only [oracleCalls_bind]
  rw [classifyState_oracleCalls_zero]
  simp only [Nat.zero_add]
  cases hkind : (CountingMatroid.Program.classifyState current.state).val with
  | invalid => simp [oracleCalls]
  | defect i j => simp [countIncrement, oracleCalls]
  | transversal =>
      have hr := pairedRank_oracleCalls_le r o₁ o₂ current.state
      have hp := ratPower_oracleCalls_zero rho
        (n - (pairedRank r o₁ o₂ current.state).val)
      simp [countIncrement, natSub, ratAdd, oracleCalls] at hr hp ⊢
      omega

/-- INTERNAL: A capped integer draw only reads fair bits and uses word operations.
TEXLINE: main.tex:1392-1421 -/
theorem boundedUniform_oracleCalls_zero (tape : ℕ → Bool)
    (trials v cursor : ℕ) :
    oracleCalls (CountingMatroid.Program.boundedUniform tape trials v cursor) = 0 := by
  have hbits (width start : ℕ) :
      oracleCalls (Arlib.Computation.Charged.repeatFor
        (fun _ inner => do
          let bit ← fairBit tape inner.2
          let value ← appendBit inner.1 bit
          Prod.mk value <$> successor inner.2) width (0, start)) = 0 := by
    apply Nat.eq_zero_of_le_zero
    apply oracleCalls_repeatFor_le (k := 0)
    intro _ _
    simp [fairBit, appendBit, successor, oracleCalls]
  have htrials (width : ℕ) : ∀ acc,
      oracleCalls (do
        let done ← isSome acc.1
        if done then pure acc
        else
          let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
            let bit ← fairBit tape inner.2
            let value ← appendBit inner.1 bit
            let next ← successor inner.2
            pure (value, next)) width (0, acc.2)
          let accepted ← lessThan trial.1 v
          if accepted then pure (some trial.1, trial.2)
          else pure (none, trial.2)) = 0 := by
    intro acc
    by_cases hd : acc.1.isSome
    · simp [isSome, hd, oracleCalls]
    · simp [isSome, hd, oracleCalls_bind]
      refine ⟨by simp [oracleCalls], hbits width acc.2,
        by simp [lessThan, oracleCalls], ?_⟩
      split_ifs <;> simp [oracleCalls]
  unfold CountingMatroid.Program.boundedUniform
  by_cases hv : v < 1
  · simp [lessThan, hv, oracleCalls]
  · by_cases hs : v < 2
    · simp [lessThan, hv, hs, oracleCalls]
    · have hloop := oracleCalls_repeatFor_le (k := 0)
        (f := fun _ acc => do
          let done ← isSome acc.1
          if done then pure acc
          else
            let trial ← Arlib.Computation.Charged.repeatFor (fun _ inner => do
              let bit ← fairBit tape inner.2
              let value ← appendBit inner.1 bit
              let next ← successor inner.2
              pure (value, next)) ((v - 1).log2 + 1) (0, acc.2)
            let accepted ← lessThan trial.1 v
            if accepted then pure (some trial.1, trial.2)
            else pure (none, trial.2))
        (by intro _ acc; exact le_of_eq (htrials _ acc))
        trials ((none : Option ℕ), cursor)
      simp [lessThan, hv, hs, uniformWidth, oracleCalls] at hloop ⊢
      omega

/-- INTERNAL: Visiting a paired label to select an occupied or free element
does not query an independence oracle. -/
theorem selectionVisit_oracleCalls_zero {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ)
    (acc : Option (PairedGround n) × ℕ) (element : PairedGround n) :
    oracleCalls (CountingMatroid.Program.selectionVisit state occupied k acc element) =
      0 := by
  unfold CountingMatroid.Program.selectionVisit
  cases occupied <;>
    by_cases hi : element ∈ state <;>
    by_cases hk : acc.2 = k <;>
    simp [containsPaired, natEqual, successor, oracleCalls, hi, hk]

/-- INTERNAL: Both scans in a paired-label selection use only word operations. -/
theorem selectPaired_oracleCalls_zero {n : ℕ} (state : PairedSet n)
    (occupied : Bool) (k : ℕ) :
    oracleCalls (CountingMatroid.Program.selectPaired state occupied k) = 0 := by
  unfold CountingMatroid.Program.selectPaired
  have hinner : ∀ (acc : Option (PairedGround n) × ℕ) (i : Fin n),
      oracleCalls (Arlib.Computation.Charged.foldl
        (CountingMatroid.Program.selectionVisit state occupied k)
        [((i, false) : PairedGround n), (i, true)] acc) ≤ 0 := by
    intro acc i
    have h := oracleCalls_foldl_le _ 0
      (by intro b a; exact Nat.le_zero.mpr (selectionVisit_oracleCalls_zero state occupied k b a))
      [((i, false) : PairedGround n), (i, true)] acc
    simpa using h
  have h := oracleCalls_foldl_le _ 0 hinner (List.finRange n)
    ((none : Option (PairedGround n)), 0)
  have hz : oracleCalls (Arlib.Computation.Charged.foldl _ (List.finRange n)
      ((none : Option (PairedGround n)), 0)) = 0 :=
    Nat.eq_zero_of_le_zero (by simpa using h)
  simp only [oracleCalls_bind]
  rw [hz]
  simp [oracleCalls]

/-- INTERNAL: The rational acceptance comparison uses no independence query.
TEXLINE: main.tex:1392-1421 -/
theorem acceptance_oracleCalls_zero {n : ℕ} (tape : ℕ → Bool)
    (drawTrials : ℕ) (oldWeight newWeight : ℚ)
    (state candidate : PairedSet n) (cursor : ℕ) :
    oracleCalls (do
      let ratio ← ratDiv newWeight oldWeight
      let needsDraw ← ratLess ratio 1
      if needsDraw then
        let denominator ← rationalDenominator ratio
        let numerator ← rationalNumerator ratio
        let acceptedDraw ← CountingMatroid.Program.boundedUniform tape drawTrials
          denominator cursor
        match acceptedDraw.1 with
        | none => pure none
        | some value =>
            let accepted ← lessThan value numerator
            if accepted then pure (some (candidate, acceptedDraw.2))
            else pure (some (state, acceptedDraw.2))
      else pure (some (candidate, cursor))) = 0 := by
  simp only [oracleCalls_bind]
  have hdiv : oracleCalls (ratDiv newWeight oldWeight) = 0 := by
    simp [ratDiv, oracleCalls]
  have hless : ∀ a b : ℚ, oracleCalls (ratLess a b) = 0 := by
    intro a b
    simp [ratLess, oracleCalls]
  have hden : ∀ a : ℚ, oracleCalls (rationalDenominator a) = 0 := by
    intro a
    simp [rationalDenominator, oracleCalls]
  have hnum : ∀ a : ℚ, oracleCalls (rationalNumerator a) = 0 := by
    intro a
    simp [rationalNumerator, oracleCalls]
  simp only [hdiv, hless, Nat.zero_add]
  split_ifs
  · simp only [oracleCalls_bind]
    simp only [hden, hnum, Nat.zero_add]
    rw [boundedUniform_oracleCalls_zero]
    simp only [Nat.zero_add]
    split
    · simp [oracleCalls]
    · simp [lessThan, oracleCalls]
      split_ifs <;> simp
  · simp [oracleCalls]

end CountingMatroid.Analysis.ResourceBound
