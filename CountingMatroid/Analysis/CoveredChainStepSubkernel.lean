import CountingMatroid.Analysis.ExchangeProposalGeometry
import CountingMatroid.Analysis.ChainStepIntervalReplay
import CountingMatroid.Analysis.BoundedUniformAbortMass
import CountingMatroid.Analysis.ClassifiedStateSelection

set_option autoImplicit false

/-!
The one-transition finite-bit subkernel needed for recorded observation paths.
Only successful transitions whose consumed interval fits in the supplied suffix
are counted. This isolates rejection sampling and Metropolis acceptance from
the quantitative whole-run coverage and stopping-prefix composition arguments.
The zero-length suffix case is proved. On nonsingleton grounds, the comparison
also holds for suffixes shorter than a nonholding attempt's first index word
plus its laziness bit, and for every suffix length when the trial cap is zero.
The remaining successful-draw transition comparison is open.
-/

namespace CountingMatroid.Analysis.CoveredChainStepSubkernel

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: Successful transition mass with the final consumed cursor
inside the actual finite fair suffix. Abort paths contribute zero.
TEXLINE: main.tex:746-751,1392-1421 -/
noncomputable def coveredChainStepMass {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ)
    (weights : Multipliers n) (head : List Bool) (t : ℕ)
    (state next : PairedSet n) : ℝ := by
  classical
  exact ∑ suffix : List.Vector Bool t,
    if ∃ stop : ℕ, stop ≤ head.length + t ∧
      (chainStep r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
        trials q weights state head.length).val = some (next, stop)
    then 1 / (2 : ℝ) ^ t else 0

/-- INTERNAL: A successful nonsingleton integer draw consumes at least one
whole rejection word; this excludes success using defaulted bits in a suffix
shorter than that word.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_success_consumes_word
    (tape : ℕ → Bool) (trials v start value stop : ℕ) (hv : 2 ≤ v)
    (h : (boundedUniform tape trials v start).val = (some value, stop)) :
    start + ((v - 1).log2 + 1) ≤ stop := by
  rw [BoundedUniformAbortMass.boundedUniform_value tape trials v start hv] at h
  induction trials generalizing start with
  | zero => cases h
  | succ trials ih =>
    simp only [BoundedUniformAbortMass.sampleWords, Option.isSome_none,
      Bool.false_eq_true, ite_false] at h
    split at h
    · rw [BoundedUniformAbortMass.sampleWords_some] at h
      have hc := congrArg Prod.snd h
      rw [BoundedUniformAbortMass.readWord_cursor] at hc
      exact hc.le
    · have hc := ih (BoundedUniformAbortMass.readWord tape
        ((v - 1).log2 + 1) 0 start).2 h
      rw [BoundedUniformAbortMass.readWord_cursor] at hc
      omega

/-- INTERNAL: Every nonholding successful chain attempt on a nonsingleton
ground consumes a complete first index word after its laziness bit.
TEXLINE: main.tex:746-751,1392-1401 -/
theorem chain_step_nonhold_consumes_word {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state next : PairedSet n) (start stop : ℕ) (hn : 2 ≤ n)
    (hb : tape start = false)
    (h : (chainStep r o₁ o₂ tape trials q weights state start).val =
      some (next, stop)) : start + 1 + ((n - 1).log2 + 1) ≤ stop := by
  unfold chainStep at h
  simp +instances only [Arlib.Computation.Charged.val_bind,
    Model.Operations.fairBit, Model.Operations.successor,
    Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true, ite_false] at h
  cases ha : (boundedUniform tape trials n (start + 1)).val with
  | mk choice stopA =>
    cases choice with
    | none =>
      simp +instances only [ha, Arlib.Computation.Charged.val_pure] at h
      cases h
    | some value =>
      simp +instances only [ha, Arlib.Computation.Charged.val_bind] at h
      have hA := bounded_uniform_success_consumes_word tape trials n
        (start + 1) value stopA hn ha
      have hB := (BoundedUniformReplay.boundedUniform_interval_replay
        trials n stopA tape).1
      have hC (v : ℕ) := (BoundedUniformReplay.boundedUniform_interval_replay
        trials v (boundedUniform tape trials n stopA).val.2 tape).1
      dsimp only at hB hC
      split at h
      · cases h
      · simp +instances only [Arlib.Computation.Charged.val_bind] at h
        split at h
        · simp +instances only [Arlib.Computation.Charged.val_bind,
            Model.Operations.erasePaired, Model.Operations.insertPaired,
            Arlib.Computation.Charged.val_opMany] at h
          split at h
          · have he := congrArg (fun out => out.map Prod.snd) h
            simp only [Arlib.Computation.Charged.val_pure, Option.map_some, Option.some.injEq] at he
            omega
          · simp +instances only [Arlib.Computation.Charged.val_bind] at h
            split at h
            · rename_i old new ho hn
              simp +instances only [Arlib.Computation.Charged.val_bind] at h
              split at h
              · simp +instances only [Arlib.Computation.Charged.val_bind,
                  Model.Operations.ratDiv, Model.Operations.rationalDenominator,
                  Model.Operations.rationalNumerator,
                  Arlib.Computation.Charged.val_opMany] at h
                have hc := hC (new / old).den
                split at h
                · cases h
                · simp +instances only [Arlib.Computation.Charged.val_bind] at h
                  split at h
                  all_goals
                    have he := congrArg (fun out => out.map Prod.snd) h
                    simp only [Arlib.Computation.Charged.val_pure, Option.map_some, Option.some.injEq] at he
                    omega
              · have he := congrArg (fun out => out.map Prod.snd) h
                simp only [Arlib.Computation.Charged.val_pure, Option.map_some, Option.some.injEq] at he
                omega
            · cases h
        · cases h

/-- INTERNAL: If covered successes force the laziness bit, their finite
suffix mass is at most one-half at the original state and zero elsewhere.
TEXLINE: main.tex:746-751 -/
theorem covered_chain_mass_forced_hold {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ)
    (weights : Multipliers n) (head : List Bool) (t : ℕ)
    (state next : PairedSet n) (ht : 0 < t)
    (hhold : ∀ (suffix : List.Vector Bool t) stop,
      stop ≤ head.length + t →
      (chainStep r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
        trials q weights state head.length).val = some (next, stop) →
      ((head ++ suffix.val)[head.length]?).getD false = true) :
    coveredChainStepMass r o₁ o₂ trials q weights head t state next ≤
      if state = next then (1 / 2 : ℝ) else 0 := by
  classical
  let event := fun suffix : List.Vector Bool t => ∃ stop : ℕ,
    stop ≤ head.length + t ∧
      (chainStep r o₁ o₂ (fun i => ((head ++ suffix.val)[i]?).getD false)
        trials q weights state head.length).val = some (next, stop)
  have hbit (suffix : List.Vector Bool t) (hs : event suffix) :
      suffix.get ⟨0, ht⟩ = true := by
    obtain ⟨stop, hstop, hrun⟩ := hs
    have hb := hhold suffix stop hstop hrun
    rw [List.getElem?_append_right (by omega), Nat.sub_self,
      List.getElem?_eq_getElem (by simpa only [suffix.property] using ht),
      Option.getD_some] at hb
    exact hb
  by_cases heq : state = next
  · rw [if_pos heq]
    have hc := BoundedUniformAbortMass.forced_bits_card t {⟨0, ht⟩} event (by
      intro suffix hs i hi
      have hi0 : i = ⟨0, ht⟩ := Finset.mem_singleton.mp hi
      subst i
      exact hbit suffix hs)
    simp only [Finset.card_singleton] at hc
    have hm : coveredChainStepMass r o₁ o₂ trials q weights head t state next =
        ((Finset.univ.filter event).card : ℝ) / (2 : ℝ) ^ t := by
      unfold coveredChainStepMass
      change (∑ suffix : List.Vector Bool t,
        if event suffix then 1 / (2 : ℝ) ^ t else 0) = _
      rw [← Finset.sum_filter]
      simp only [Finset.sum_const, nsmul_eq_mul, mul_one_div]
    rw [hm]
    calc
      _ ≤ ((2 ^ (t - 1) : ℕ) : ℝ) / (2 : ℝ) ^ t := by
        exact div_le_div_of_nonneg_right (Nat.cast_le.mpr (by
          convert hc using 1
          congr 1
          ext suffix
          simp only [Finset.mem_filter])) (by positivity)
      _ = 1 / 2 := by
        rw [Nat.cast_pow, Nat.cast_ofNat,
          show (2 : ℝ) ^ t = 2 ^ (t - 1) * 2 by
            conv_lhs => rw [show t = (t - 1) + 1 by omega]
            rw [pow_succ]]
        have hp : (2 : ℝ) ^ (t - 1) ≠ 0 := by positivity
        field_simp
  · rw [if_neg heq]
    have hz : coveredChainStepMass r o₁ o₂ trials q weights head t state next = 0 := by
      unfold coveredChainStepMass
      apply Finset.sum_eq_zero
      intro suffix _
      apply if_neg
      rintro ⟨stop, hstop, hrun⟩
      have hb := hhold suffix stop hstop hrun
      simp only [chainStep, Arlib.Computation.Charged.val_bind,
        Model.Operations.fairBit, Model.Operations.successor,
        Arlib.Computation.Charged.val_op, hb, ite_true,
        Arlib.Computation.Charged.val_pure, Option.some.injEq, Prod.mk.injEq] at hrun
      exact heq hrun.1
    exact hz.le

/-- INTERNAL: Covered successful one-step sublaw is dominated by the ideal
Metropolis transition. The starting state has the program's valid n-element
shape. The consumed-cursor restriction prevents defaulted bits from acting
as additional fair randomness; no global schedule or warm law is used here.
TEXLINE: main.tex:746-751,1392-1421 -/
theorem covered_chain_step_subkernel {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (trials : ℕ) (q : ℚ)
    (weights : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ a, 0 < weights a) (head : List Bool) (t : ℕ)
    (state next : PairedSet n) (hcard : state.card = n)
    (hvalid : (classifyState state).val ≠ .invalid) :
    coveredChainStepMass r o₁ o₂ trials q weights head t state next ≤
      idealChain r o₁ o₂ q weights hn hq hw state next := by
  classical
  by_cases ht : t = 0
  · subst t
    have hzero : coveredChainStepMass r o₁ o₂ trials q weights head 0 state next = 0 := by
      unfold coveredChainStepMass
      apply Finset.sum_eq_zero
      intro suffix _
      apply if_neg
      rintro ⟨stop, hstop, hrun⟩
      have hreplay := ChainStepIntervalReplay.chainStep_success_interval
        r o₁ o₂ trials q weights state head.length
        (fun i => ((head ++ suffix.val)[i]?).getD false) (next, stop) hrun
      have heq := hreplay.2 (fun _ => true) (by
        intro i hlo hhi
        dsimp only at hhi
        omega)
      simp only [chainStep, Arlib.Computation.Charged.val_bind,
        Model.Operations.fairBit, Model.Operations.successor,
        Arlib.Computation.Charged.val_op, ite_true,
        Arlib.Computation.Charged.val_pure, Option.some.injEq,
        Prod.mk.injEq] at heq
      omega
    rw [hzero]
    exact (idealChain r o₁ o₂ q weights hn hq hw).coe_nonneg state next
  · have htpos : 0 < t := Nat.pos_of_ne_zero ht
    by_cases hsmall : 2 ≤ n ∧ (t ≤ (n - 1).log2 + 1 ∨ trials = 0)
    · have hm := covered_chain_mass_forced_hold r o₁ o₂ trials q weights
        head t state next htpos (by
          intro suffix stop hstop hrun
          cases hb : ((head ++ suffix.val)[head.length]?).getD false with
          | true => rfl
          | false =>
            rcases hsmall.2 with hshort | hcap
            · have hc := chain_step_nonhold_consumes_word r o₁ o₂
                (fun i => ((head ++ suffix.val)[i]?).getD false)
                trials q weights state next head.length stop hsmall.1 hb hrun
              omega
            · subst trials
              have hd : (boundedUniform
                  (fun i => ((head ++ suffix.val)[i]?).getD false)
                  0 n (head.length + 1)).val = (none, head.length + 1) := by
                rw [BoundedUniformAbortMass.boundedUniform_value _ 0 n _ hsmall.1]
                rfl
              simp +instances only [chainStep, Arlib.Computation.Charged.val_bind,
                Model.Operations.fairBit, Model.Operations.successor,
                Arlib.Computation.Charged.val_op, hb, Bool.false_eq_true,
                ite_false, hd, Arlib.Computation.Charged.val_pure] at hrun
              cases hrun)
      apply hm.trans
      by_cases heq : state = next
      · subst next
        rw [if_pos rfl]
        exact ExchangeProposalGeometry.ideal_chain_lazy r o₁ o₂ q weights hn hq hw state hcard
      · rw [if_neg heq]
        exact (idealChain r o₁ o₂ q weights hn hq hw).coe_nonneg state next
    · -- Concrete route: split the laziness bit, group the two index draws
      -- and acceptance draw by their consumed stopping prefixes, and use
      -- exchange_proposal_average to identify the ideal proposal. The joint
      -- successful boundedUniform value/cursor law is required here; the
      -- abort bound and interval replay alone do not supply that law.
      -- BLOCKER (missing local lemma): for v ≥ 2, width = (v - 1).log2 + 1,
      -- k < trials, a < v, and (k + 1) * width ≤ t, the fair-suffix mass
      -- of boundedUniform returning (some a, head.length + (k + 1) * width)
      -- must be identified as
      --   ((2 ^ width - v : ℕ) : ℝ) ^ k / (2 : ℝ) ^ ((k + 1) * width).
      -- This value/cursor law, followed by fresh-suffix conditioning, supplies
      -- both the uniform proposal indices and the rational acceptance/rejection
      -- probabilities. forced_bits_card only bounds aborts or holding paths;
      -- interval replay identifies cylinders but does not count accepted words.
      -- The subsequent selector bridge must identify the index-to-element
      -- maps as bijections onto state and stateᶜ. classified_state_selection
      -- establishes lookup existence, but not that uniformity statement.
      unfold coveredChainStepMass
      sorry

end CountingMatroid.Analysis.CoveredChainStepSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · proved minimum successful integer-word consumption, propagated it through every nonholding chain leaf, and bounded holding-only covered mass by one-half. The target now closes when n ≥ 2 and t ≤ (n - 1).log2 + 1, or when n ≥ 2 and trials = 0. The remaining obligation is the successful value/cursor counting law, with its required formula recorded at the open branch; no new proof debt introduced.
* 2026-10-09 · decomposed · isolated the covered one-transition comparison; zero suffix mass follows by replay onto an all-holding tape. Positive-length comparison needs successful rejection-word counting, then the established proposal geometry.
-/
