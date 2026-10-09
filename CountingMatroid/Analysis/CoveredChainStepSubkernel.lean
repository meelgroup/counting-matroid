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
The zero-length suffix case is proved; positive-length transition comparison
remains open.
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
  · -- Concrete route: split the laziness bit, group the two index draws
    -- and acceptance draw by their consumed stopping prefixes, and use
    -- exchange_proposal_average to identify the ideal proposal. The joint
    -- successful boundedUniform value/cursor law is required here; the
    -- abort bound and interval replay alone do not supply that law.
    -- A compiled scratch probe split state = next and rewrote the ideal
    -- side with metropolis_apply_self / metropolis_apply_of_ne. The latter
    -- exposes proposal * min 1 (newWeight / oldWeight); the former exposes
    -- one minus the off-diagonal rate sum. Both still require grouping
    -- successful integer draws rather than a pointwise suffix comparison.
    -- BLOCKER: uniform successful rejection-word counts at each stopping
    -- cursor, including acceptance and rejection branches of the rational draw.
    unfold coveredChainStepMass
    sorry

end CountingMatroid.Analysis.CoveredChainStepSubkernel

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · decomposed · isolated the covered one-transition comparison; zero suffix mass follows by replay onto an all-holding tape. Positive-length comparison needs successful rejection-word counting, then the established proposal geometry.
-/
