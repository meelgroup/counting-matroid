import CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Compose the three adaptive draw subkernels and the initial fair holding
bit in the selection-index coordinates of the executable chain. -/
namespace CountingMatroid.Analysis.CoveredChainIndexedSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Analysis.SelectedPairedBijection
open CountingMatroid.Analysis.SelectedMetropolisKernel
open CountingMatroid.Analysis.RationalAcceptanceSubkernel
open CountingMatroid.Analysis.ProgramExchangeAcceptanceSubkernel
open CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: The erase/insert proposal made by the two uniform selection indices. -/
def indexedCandidate {n : ℕ} (state : PairedSet n) (hcard : state.card = n)
    (i j : Fin n) : PairedSet n :=
  insert (selectedLabel state false hcard j).val
    (state.erase (selectedLabel state true hcard i).val)

/-- INTERNAL: Once the two index draws are fixed, the actual chain step is
precisely its remaining classifier/weight/acceptance continuation. -/
theorem chain_step_after_draws {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n) (state : PairedSet n)
    (hcard : state.card = n) (tape : ℕ → Bool) (start stopA stopB : ℕ)
    (i j : Fin n) (hhold : tape start = false)
    (ha : (boundedUniform tape trials n (start + 1)).val = (some i.val, stopA))
    (hb : (boundedUniform tape trials n stopA).val = (some j.val, stopB)) :
    (chainStep r o₁ o₂ tape trials q weights state start).val =
      proposalAttempt r o₁ o₂ trials q weights state
        (indexedCandidate state hcard i j) tape stopB := by
  simp +instances only [chainStep, Arlib.Computation.Charged.val_bind,
    Model.Operations.fairBit, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hhold, Bool.false_eq_true, ite_false,
    ha, hb, select_paired_selectedLabel state true hcard i,
    select_paired_selectedLabel state false hcard j,
    Model.Operations.erasePaired, Model.Operations.insertPaired,
    Arlib.Computation.Charged.val_opMany]
  cases hk : (classifyState (indexedCandidate state hcard i j)).val <;>
    simp +instances only [proposalAttempt, indexedCandidate] at hk ⊢
  all_goals
    simp +instances only [hk, reduceCtorEq, if_false, if_true, Arlib.Computation.Charged.val_pure,
      Arlib.Computation.Charged.val_bind]
  all_goals
    cases ho : (weightOfKind r o₁ o₂ q weights state (classifyState state).val).val <;>
    cases hn : (weightOfKind r o₁ o₂ q weights
      (indexedCandidate state hcard i j) (classifyState (indexedCandidate state hcard i j)).val).val <;>
    simp +instances [indexedCandidate, hk] at hn <;>
    simp +instances [ho, hn, rationalAccept, Model.Operations.ratDiv,
      Model.Operations.ratLess, Model.Operations.rationalDenominator,
      Model.Operations.rationalNumerator, Model.Operations.lessThan]
  all_goals
    split <;> simp +instances only [*, Arlib.Computation.Charged.val_pure,
      Arlib.Computation.Charged.val_bind, Arlib.Computation.Charged.val_opMany,
      Arlib.Computation.Charged.val_op]
  all_goals
    split <;> simp +instances [*, Arlib.Computation.Charged.val_bind,
      Arlib.Computation.Charged.val_pure, Arlib.Computation.Charged.val_op]

  all_goals split_ifs <;> rfl

/-- INTERNAL: Split a fair suffix by its first Boolean bit. -/
theorem fair_mass_split_bit (head : List Bool) (t : ℕ) (ht : 0 < t)
    (E : (ℕ → Bool) → Prop) :
    fairMass head t E = (1 / 2 : ℝ) * fairMass (head ++ [true]) (t - 1) E +
      (1 / 2 : ℝ) * fairMass (head ++ [false]) (t - 1) E := by
  classical
  rw [fairMass_split head t 1 (by omega)]
  let singleton := fun b : Bool => (⟨[b], rfl⟩ : List.Vector Bool 1)
  have hbij : Function.Bijective singleton := by
    constructor
    · intro a b h
      have hv := congrArg Subtype.val h
      exact List.cons.inj hv |>.1
    · intro bits
      obtain ⟨b, hb⟩ := List.length_eq_one_iff.mp bits.property
      exact ⟨b, Subtype.ext hb.symm⟩
  rw [← @Fintype.sum_bijective Bool (List.Vector Bool 1) ℝ _ _ _ singleton hbij
    (fun b => (1 / (2 : ℝ) ^ 1) * fairMass (head ++ (singleton b).val) (t-1) E)
    (fun pref : List.Vector Bool 1 => (1 / (2 : ℝ) ^ 1) * fairMass (head ++ pref.val) (t-1) E)
    (fun _ => rfl), Fintype.sum_bool]
  simp only [pow_one]
  rfl

/-- INTERNAL: Each indexed Metropolis accept/reject outcome has nonnegative mass. -/
theorem indexed_outcome_nonneg {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (weights : Multipliers n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state candidate next : PairedSet n) :
    0 ≤ exchangeOutcome state candidate next (min 1
      ((operationalLaw r o₁ o₂ q weights hq hw) candidate /
        (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  let π := operationalLaw r o₁ o₂ q weights hq hw
  have hp : 0 ≤ min 1 (π candidate / π state) :=
    le_min zero_le_one (div_nonneg (π.coe_nonneg candidate) (π.coe_nonneg state))
  have hple : min 1 (π candidate / π state) ≤ 1 := min_le_left _ _
  apply add_nonneg
  · exact mul_nonneg hp (by split_ifs <;> positivity)
  · exact mul_nonneg (sub_nonneg.mpr hple) (by split_ifs <;> positivity)

/-- INTERNAL: Compose both adaptive index draws with their final proposal
continuation, summing the stopped endpoints of each before the next draw.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem two_draw_proposal_mass {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n)
    (hvalid : (classifyState state).val ≠ .invalid) (head : List Bool) (t : ℕ) :
    fairMass head t (fun tape => ∃ (i : Fin n) (stopA : ℕ),
      stopA ≤ head.length + t ∧
      (boundedUniform tape trials n head.length).val = (some i.val, stopA) ∧
      ∃ (j : Fin n) (stopB : ℕ), stopB ≤ head.length + t ∧
      (boundedUniform tape trials n stopA).val = (some j.val, stopB) ∧
      ∃ stop, stop ≤ head.length + t ∧
      proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
        tape stopB = some (next, stop)) ≤
    (1 / (n : ℝ)) * ∑ i : Fin n, (1 / (n : ℝ)) * ∑ j : Fin n,
      exchangeOutcome state (indexedCandidate state hcard i j) next (min 1
        ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
          (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  let outcome := fun i j : Fin n =>
    exchangeOutcome state (indexedCandidate state hcard i j) next (min 1
      ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
        (operationalLaw r o₁ o₂ q weights hq hw) state))
  have hpos (i j : Fin n) : 0 ≤ outcome i j :=
    indexed_outcome_nonneg r o₁ o₂ q weights hq hw state _ next
  apply bounded_uniform_bind_mass head trials n t hn _
    (fun i => (1 / (n : ℝ)) * ∑ j : Fin n, outcome i j)
    (fun i => mul_nonneg (by positivity) (Finset.sum_nonneg (fun j _ => hpos i j)))
  intro i stopA hloA hhiA prefA hdrawA
  let headA := head ++ prefA.val
  let tA := t - (stopA - head.length)
  have hlenA : headA.length = stopA := by
    simp only [headA, List.length_append, prefA.property]
    omega
  have hendA : stopA + tA = head.length + t := by dsimp [tA]; omega
  have hbound := bounded_uniform_bind_mass headA trials n tA hn
    (fun j tape stopB => ∃ stop, stop ≤ head.length + t ∧
      proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
        tape stopB = some (next, stop)) (outcome i) (hpos i) (by
    intro j stopB hloB hhiB prefB hdrawB
    let headB := headA ++ prefB.val
    let tB := tA - (stopB - headA.length)
    have hlenB : headB.length = stopB := by
      simp only [headB, List.length_append, prefB.property]
      omega
    have hendB : stopB + tB = head.length + t := by
      dsimp [tB]
      omega
    have hp := proposal_attempt_covered_mass r o₁ o₂ trials q weights hq hw
      state (indexedCandidate state hcard i j) next hvalid headB tB
    simpa only [hlenB, hendB] using hp)
  simpa only [hlenA, hendA] using hbound

/-- INTERNAL: A nonholding successful chain step exposes the two successful
index draws and its final proposal continuation, all with monotone cursors. -/
theorem chain_step_nonholding_success {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state next : PairedSet n) (hcard : state.card = n) (tape : ℕ → Bool)
    (start stop : ℕ) (hhold : tape start = false)
    (hrun : (chainStep r o₁ o₂ tape trials q weights state start).val = some (next, stop)) :
    ∃ (i j : Fin n) (stopA stopB : ℕ),
      (boundedUniform tape trials n (start + 1)).val = (some i.val, stopA) ∧
      (boundedUniform tape trials n stopA).val = (some j.val, stopB) ∧
      proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
        tape stopB = some (next, stop) ∧
      start + 1 ≤ stopA ∧ stopA ≤ stopB ∧ stopB ≤ stop := by
  cases ha : (boundedUniform tape trials n (start + 1)).val with
  | mk choice stopA =>
    cases choice with
    | none =>
      simp +instances only [chainStep, Arlib.Computation.Charged.val_bind,
        Model.Operations.fairBit, Model.Operations.successor,
        Arlib.Computation.Charged.val_op, hhold, Bool.false_eq_true, ite_false,
        ha, Arlib.Computation.Charged.val_pure] at hrun
      cases hrun
    | some a =>
      cases hb : (boundedUniform tape trials n stopA).val with
      | mk choiceB stopB =>
        cases choiceB with
        | none =>
          simp +instances only [chainStep, Arlib.Computation.Charged.val_bind,
            Model.Operations.fairBit, Model.Operations.successor,
            Arlib.Computation.Charged.val_op, hhold, Bool.false_eq_true, ite_false,
            ha, hb, Arlib.Computation.Charged.val_pure] at hrun
          cases hrun
        | some b =>
          have halt := ObservationRoundDrawSites.boundedUniform_result_lt
            tape trials n (start + 1) a (by rw [ha])
          have hblt := ObservationRoundDrawSites.boundedUniform_result_lt
            tape trials n stopA b (by rw [hb])
          let i : Fin n := ⟨a, halt⟩
          let j : Fin n := ⟨b, hblt⟩
          have hp := (chain_step_after_draws r o₁ o₂ trials q weights state hcard
            tape start stopA stopB i j hhold ha hb).symm.trans hrun
          have hA := (BoundedUniformReplay.boundedUniform_interval_replay
            trials n (start + 1) tape).1
          have hB := (BoundedUniformReplay.boundedUniform_interval_replay
            trials n stopA tape).1
          simp only [ha] at hA
          simp only [hb] at hB
          exact ⟨i, j, stopA, stopB, rfl, hb, hp, hA, hB,
            proposal_attempt_monotone r o₁ o₂ trials q weights state _ next tape stopB stop hp⟩

/-- INTERNAL: The full covered finite-bit chain mass is bounded by the
lazy uniform-index accept/reject kernel, including both short and long tapes.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem covered_chain_indexed_mass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (hn : 0 < n) (hq : 0 < q) (hw : ∀ a, 0 < weights a)
    (state next : PairedSet n) (hcard : state.card = n)
    (hvalid : (classifyState state).val ≠ .invalid)
    (head : List Bool) (t : ℕ) (ht : 0 < t) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (chainStep r o₁ o₂ tape trials q weights state head.length).val = some (next, stop)) ≤
      (1 / 2 : ℝ) * (if state = next then 1 else 0) +
      (1 / (2 * (n : ℝ) ^ 2)) * ∑ i : Fin n, ∑ j : Fin n,
        exchangeOutcome state (indexedCandidate state hcard i j) next (min 1
          ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
            (operationalLaw r o₁ o₂ q weights hq hw) state)) := by
  classical
  let E := fun tape => ∃ stop, stop ≤ head.length + t ∧
    (chainStep r o₁ o₂ tape trials q weights state head.length).val = some (next, stop)
  let outcome := fun i j : Fin n => exchangeOutcome state (indexedCandidate state hcard i j)
    next (min 1 ((operationalLaw r o₁ o₂ q weights hq hw) (indexedCandidate state hcard i j) /
      (operationalLaw r o₁ o₂ q weights hq hw) state))
  have hholding : fairMass (head ++ [true]) (t - 1) E ≤
      if state = next then (1 : ℝ) else 0 := by
    by_cases heq : state = next
    · rw [if_pos heq]
      exact fair_mass_le_one _ _ _
    · rw [if_neg heq]
      have hz : fairMass (head ++ [true]) (t - 1) E = 0 := by
        unfold fairMass
        apply Finset.sum_eq_zero
        intro bits _
        apply if_neg
        rintro ⟨stop, hstop, hrun⟩
        have hb : finiteTape ((head ++ [true]) ++ bits.val) head.length = true := by
          unfold finiteTape
          rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
          simp
        simp only [chainStep, Arlib.Computation.Charged.val_bind,
          Model.Operations.fairBit, Model.Operations.successor,
          Arlib.Computation.Charged.val_op, hb, ite_true,
          Arlib.Computation.Charged.val_pure, Option.some.injEq, Prod.mk.injEq] at hrun
        exact heq hrun.1
      exact hz.le
  have hnonholding : fairMass (head ++ [false]) (t - 1) E ≤
      (1 / (n : ℝ)) * ∑ i : Fin n, (1 / (n : ℝ)) * ∑ j : Fin n, outcome i j := by
    have hlen : (head ++ [false]).length = head.length + 1 := by simp
    have hend : (head ++ [false]).length + (t - 1) = head.length + t := by
      rw [hlen]
      omega
    apply le_trans (fairMass_mono (head ++ [false]) (t - 1) E
      (fun tape => ∃ (i : Fin n) (stopA : ℕ),
        stopA ≤ (head ++ [false]).length + (t - 1) ∧
        (boundedUniform tape trials n (head ++ [false]).length).val = (some i.val, stopA) ∧
        ∃ (j : Fin n) (stopB : ℕ), stopB ≤ (head ++ [false]).length + (t - 1) ∧
        (boundedUniform tape trials n stopA).val = (some j.val, stopB) ∧
        ∃ stop, stop ≤ (head ++ [false]).length + (t - 1) ∧
        proposalAttempt r o₁ o₂ trials q weights state (indexedCandidate state hcard i j)
          tape stopB = some (next, stop)) (by
      intro bits hs
      obtain ⟨stop, hstop, hrun⟩ := hs
      have hb : finiteTape ((head ++ [false]) ++ bits.val) head.length = false := by
        unfold finiteTape
        rw [List.append_assoc, List.getElem?_append_right (Nat.le_refl _)]
        simp
      obtain ⟨i, j, stopA, stopB, ha, hb, hp, hmA, hmB, hmC⟩ :=
        chain_step_nonholding_success r o₁ o₂ trials q weights state next hcard
          (finiteTape ((head ++ [false]) ++ bits.val)) head.length stop hb hrun
      refine ⟨i, stopA, by omega, ?_, j, stopB, by omega, hb, stop, by omega, hp⟩
      simpa only [hlen] using ha))
    exact two_draw_proposal_mass r o₁ o₂ trials q weights hn hq hw state next hcard hvalid
      (head ++ [false]) (t - 1)
  calc
    _ = (1 / 2 : ℝ) * fairMass (head ++ [true]) (t - 1) E +
        (1 / 2 : ℝ) * fairMass (head ++ [false]) (t - 1) E := fair_mass_split_bit head t ht E
    _ ≤ (1 / 2 : ℝ) * (if state = next then 1 else 0) +
        (1 / 2 : ℝ) * ((1 / (n : ℝ)) * ∑ i : Fin n,
          (1 / (n : ℝ)) * ∑ j : Fin n, outcome i j) :=
      add_le_add (mul_le_mul_of_nonneg_left hholding (by norm_num))
        (mul_le_mul_of_nonneg_left hnonholding (by norm_num))
    _ = _ := by
      rw [← Finset.mul_sum]
      have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
      field_simp [hnreal]
      <;> ring

end CountingMatroid.Analysis.CoveredChainIndexedSubkernel
