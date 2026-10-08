import CountingMatroid.Analysis.TransversalPartition
import Mathlib.Data.Set.Finite.List

set_option autoImplicit false

namespace CountingMatroid.Analysis.FiniteTapeProductAccuracy

open CountingMatroid.Model

/-- INTERNAL: At most one eighth of capped finite tapes yield a completed
product farther than ε/4 from the concrete final transversal partition sum.
This is the conditional restart and observation analysis, learned-weight
induction, product estimate, and uncapped-to-capped tape coupling.
TEXLINE: main.tex:1207-1315,1392-1421 -/
theorem finite_tape_product_accuracy (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (o₁ o₂ : IndependenceOracle n)
    (p : InputParams) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂)
    (hpositive : 0 < commonBaseCount M₁ M₂) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let c := CountingMatroid.Analysis.TransversalPartition.partitionSum
      r o₁ o₂ (s.ρ ^ s.L)
    (Set.ncard {bits : List Bool | bits.length = m ∧
      let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s
      y ≠ 0 ∧
        (y < (1 - p.ε / 4) * c ∨
         (1 + p.ε / 4) * c < y)} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ (1 / 8 : ENNReal) := by
  by_cases hn : n = 0
  · subst n
    have hL : (CountingMatroid.Interface.Pseudocode.setup 0 p).L = 0 := by
      unfold CountingMatroid.Interface.Pseudocode.setup CountingMatroid.Program.schedule
      simp only [Arlib.Computation.Charged.val_bind,
        Arlib.Computation.Charged.val_pure, CountingMatroid.Model.Operations.natMul,
        CountingMatroid.Model.Operations.natAdd,
        CountingMatroid.Model.Operations.ratDiv,
        Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany]
      simp
    have hrun (bits : List Bool) :
        CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false)
          (CountingMatroid.Interface.Pseudocode.setup 0 p) = (1 : ℚ) := by
      simp [CountingMatroid.Interface.Pseudocode.singleRun,
        CountingMatroid.Program.boundedRun, hL,
        CountingMatroid.Program.natPower,
        CountingMatroid.Model.Operations.ratMul,
        CountingMatroid.Model.Operations.ratOfNat,
        Arlib.Computation.Charged.repeatFor]
    have hc : CountingMatroid.Analysis.TransversalPartition.partitionSum
        r o₁ o₂ ((CountingMatroid.Interface.Pseudocode.setup 0 p).ρ ^
          (CountingMatroid.Interface.Pseudocode.setup 0 p).L) = 1 := by
      simp [CountingMatroid.Analysis.TransversalPartition.partitionSum,
        CountingMatroid.Analysis.TransversalPartition.transversalDeficiency,
        CountingMatroid.Analysis.TransversalPartition.transversalState]
    have hempty : {bits : List Bool |
        bits.length = CountingMatroid.Model.Run.blockLength 0 r p ∧
        let y := CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false)
          (CountingMatroid.Interface.Pseudocode.setup 0 p)
        y ≠ 0 ∧
          (y < (1 - p.ε / 4) * 1 ∨ (1 + p.ε / 4) * 1 < y)} = ∅ := by
      ext bits
      simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      intro h
      rw [hrun] at h
      rcases h.2.2 with hbad | hbad <;> nlinarith [p.ε_pos]
    simp only [hc, hempty, Set.ncard_empty, Nat.cast_zero, zero_mul]
    norm_num
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    -- BLOCKER (main.tex:1207-1315,1392-1421): `aesop` leaves precisely this
    -- positive-ground event-mass inequality. Unfolding the schedule and run
    -- closes only the zero-phase case above. The imported analysis has no
    -- conditional phase law for successful prior histories: in particular no
    -- restart-cap Markov bound, observation MSE bound, or learned-weight
    -- invariant. It also has no coupling of those uncapped laws to
    -- `Program.boundedRun`, which folds phase status into `Option` and returns
    -- only `(estimate, bitCursor)`. A finite-tape event bound for this exact
    -- `singleRun` is needed after that coupling; no theorem in the current
    -- imports supplies one. `Interface.Pseudocode.chainStepLaw` is defined by
    -- running `chainStep` on a finite `fairTape`; it does not identify that
    -- distribution with the paper's ideal Metropolis chain. There is no
    -- `FinChain` or `FinDist` declaration in the project for the paired-state
    -- process. Arlib has generic Markov/Chebyshev inequalities and finite-chain
    -- Metropolis stationarity, but the program-to-chain law, phase observation
    -- MSE bound, and finite-tape transfer are needed before they apply. These
    -- are same-paper proof obligations, not Prior.
    sorry

end CountingMatroid.Analysis.FiniteTapeProductAccuracy

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r13 · blocked · `exact?` and `aesop` leave the positive-ground count inequality; `chainStepLaw` is only a finite-tape PMF, and the project has no paired-state ideal-chain law or conditional phase estimate to connect it to the paper's Markov/MSE argument.
* r12 · blocked · positive-ground `exact?` and `aesop` leave the same event-mass inequality; Arlib has generic Markov/Chebyshev and Metropolis results, but no distributional bridge from `chainStep`, conditional phase law, or uncapped-to-capped coupling.
* r11 · blocked · `aesop` leaves the positive-ground event-mass inequality and `exact?` finds no matching theorem. Mathlib has Chebyshev, but the program has no finite-tape phase law, mean-square bound, or uncapped-to-capped coupling to which it applies.
* r10 · blocked · `exact?` cannot close the positive-ground event bound; source search found no finite-chain trace/MSE analysis, good-multiplier invariant, or uncapped-to-`boundedRun` coupling. The paper proves these steps at main.tex:1207-1315, so this is a same-paper dependency, not a Prior proposal.
* r9 · partial · proved the empty-ground event is empty; positive-ground `aesop` leaves the event-mass inequality, with conditional phase bounds and capped finite-tape coupling absent.
* r8 · open · `aesop` leaves the finite-tape product-event bound; no conditional phase law or uncapped-to-capped coupling is formalized.
-/
