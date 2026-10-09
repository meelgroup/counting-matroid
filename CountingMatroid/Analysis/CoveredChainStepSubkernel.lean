import CountingMatroid.Analysis.ExchangeProposalGeometry
import CountingMatroid.Analysis.ChainStepIntervalReplay
import CountingMatroid.Analysis.BoundedUniformAbortMass
import CountingMatroid.Analysis.ClassifiedStateSelection
import CountingMatroid.Analysis.BoundedUniformSuccessWords
import CountingMatroid.Analysis.BoundedUniformSubkernel
import CountingMatroid.Analysis.SelectedMetropolisKernel
import CountingMatroid.Analysis.CoveredChainIndexedSubkernel

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
The one-transition finite-bit subkernel needed for recorded observation paths.
Only successful transitions whose consumed interval fits in the supplied suffix
are counted. This isolates rejection sampling and Metropolis acceptance from
the quantitative whole-run coverage and stopping-prefix composition arguments.
The comparison is proved for every suffix length. Exact successful draw
mass is aggregated over all stopping cursors before composing fresh suffixes.
The occupied/unoccupied selector is a bijection, and the rational acceptance
branch, including its rejection contribution to the diagonal, agrees with the
ideal Metropolis accept/reject kernel.
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
  obtain ⟨k, _, hstop, _, _, _⟩ :=
    (BoundedUniformSuccessWords.bounded_uniform_success_words
      tape trials v start value stop hv).mp h
  rw [hstop]
  have hm : ((v - 1).log2 + 1) ≤ (k + 1) * ((v - 1).log2 + 1) :=
    Nat.le_mul_of_pos_left _ (by omega)
  omega

/-- INTERNAL: Every nonholding successful chain attempt on a nonsingleton
ground consumes both complete index words after its laziness bit.
TEXLINE: main.tex:746-751,1392-1401 -/
theorem chain_step_nonhold_consumes_word {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state next : PairedSet n) (start stop : ℕ) (hn : 2 ≤ n)
    (hb : tape start = false)
    (h : (chainStep r o₁ o₂ tape trials q weights state start).val =
      some (next, stop)) : start + 1 + 2 * ((n - 1).log2 + 1) ≤ stop := by
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
      cases hb : (boundedUniform tape trials n stopA).val with
      | mk choiceB stopB =>
        cases choiceB with
        | none =>
          simp +instances only [hb, Arlib.Computation.Charged.val_pure] at h
          cases h
        | some valueB =>
          simp +instances only [hb, Arlib.Computation.Charged.val_bind] at h
          have hB := bounded_uniform_success_consumes_word tape trials n
            stopA valueB stopB hn hb
          have hC (v : ℕ) := (BoundedUniformReplay.boundedUniform_interval_replay
            trials v stopB tape).1
          dsimp only at hC
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
  by_cases heq : state = next
  · rw [if_pos heq]
    have hm := BoundedUniformSubkernel.bounded_uniform_covered_mass
      head 1 2 t 1 (by omega) (by omega)
    have hbound := FiniteStoppedFiberMass.fairMass_mono head t
      (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (chainStep r o₁ o₂ tape trials q weights state head.length).val =
          some (next, stop))
      (fun tape => ∃ stop, stop ≤ head.length + t ∧
        (boundedUniform tape 1 2 head.length).val = (some 1, stop)) (by
      intro suffix hs
      obtain ⟨stop, hstop, hrun⟩ := hs
      have hb := hhold suffix stop hstop hrun
      have hb' : FiniteStoppedFiberMass.finiteTape (head ++ suffix.val) head.length = true := hb
      refine ⟨head.length + 1, by omega, ?_⟩
      rw [BoundedUniformAbortMass.boundedUniform_value _ 1 2 _ (by omega)]
      simp [BoundedUniformAbortMass.sampleWords, BoundedUniformAbortMass.readWord,
        show (2 - 1).log2 = 0 by decide, hb'])
    have hrepr : coveredChainStepMass r o₁ o₂ trials q weights head t state next =
        FiniteStoppedFiberMass.fairMass head t (fun tape =>
          ∃ stop, stop ≤ head.length + t ∧
            (chainStep r o₁ o₂ tape trials q weights state head.length).val =
              some (next, stop)) := by
      unfold coveredChainStepMass FiniteStoppedFiberMass.fairMass FiniteStoppedFiberMass.finiteTape
      apply Finset.sum_congr rfl
      intro suffix _
      split_ifs <;> rfl
    rw [hrepr]
    exact hbound.trans hm
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
    by_cases hsmall : 2 ≤ n ∧ (t ≤ 2 * ((n - 1).log2 + 1) ∨ trials = 0)
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
    · rw [SelectedMetropolisKernel.selected_metropolis_kernel
        r o₁ o₂ q weights hn hq hw state next hcard]
      have hm := CoveredChainIndexedSubkernel.covered_chain_indexed_mass
        r o₁ o₂ trials q weights hn hq hw state next hcard hvalid head t htpos
      have hrepr : coveredChainStepMass r o₁ o₂ trials q weights head t state next =
          FiniteStoppedFiberMass.fairMass head t (fun tape =>
            ∃ stop, stop ≤ head.length + t ∧
              (chainStep r o₁ o₂ tape trials q weights state head.length).val =
                some (next, stop)) := by
        unfold coveredChainStepMass FiniteStoppedFiberMass.fairMass
          FiniteStoppedFiberMass.finiteTape
        apply Finset.sum_congr rfl
        intro suffix _
        split_ifs <;> rfl
      rw [hrepr]
      simpa only [CoveredChainIndexedSubkernel.indexedCandidate] using hm

end CountingMatroid.Analysis.CoveredChainStepSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · summed covered successful draw endpoints before composition, proved the occupied/complement selector bijections, identified rational acceptance and rejection with the Metropolis outcome average, and closed the full one-step subkernel comparison. All new support declarations are proved.
* 2026-10-09 · partial · proved the successful sampler value/cursor cylinder law and fixed-endpoint continuation bound in BoundedUniformSuccessWords, used them in the holding-mass proof, and strengthened nonholding consumption to two index words. The remaining branch is split at its first fair bit; aggregating the three adaptive draws and identifying selector uniformity with the Metropolis kernel remain open. No new unproved declaration introduced.
* 2026-10-09 · partial · proved minimum successful integer-word consumption, propagated it through every nonholding chain leaf, and bounded holding-only covered mass by one-half. The target now closes when n ≥ 2 and t ≤ (n - 1).log2 + 1, or when n ≥ 2 and trials = 0. The remaining obligation is the successful value/cursor counting law, with its required formula recorded at the open branch; no new proof debt introduced.
* 2026-10-09 · decomposed · isolated the covered one-transition comparison; zero suffix mass follows by replay onto an all-holding tape. Positive-length comparison needs successful rejection-word counting, then the established proposal geometry.
-/
