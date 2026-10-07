import CountingMatroid.Model.Subroutines

set_option autoImplicit false

namespace CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines

/-- PAPER: main.tex:283-289
BORROWED: Schrijver2003, Section 41.2, Theorem 41.4.
The cited polynomial matroid-intersection pretest must be implemented on the
project's charged oracle interface, with correctness and uniform cost bounds. -/
theorem exists_feasibility_contract : Nonempty FeasibilityContract := by
  -- BLOCKER: Schrijver's cited theorem supplies an abstract polynomial oracle
  -- algorithm, but no declaration in this project, pinned Mathlib, or Arlib
  -- supplies its executable `FeasibilityImplementation.run` on the two n-bit
  -- oracles. To construct this contract, the next step must provide that code,
  -- prove its answer agrees with `decide (0 < commonBaseCount M₁ M₂)` under
  -- `FullGround`, `CommonRank`, and `ExactOracle`, and prove uniform polynomial
  -- bounds for both `oracleCalls` and `otherSteps` on the same charged run.
  -- Rephrasing these three obligations as fields of another proof-side package
  -- would leave exactly the same unproved algorithmic dependency.
  sorry

end CountingMatroid.Analysis.FeasibilitySolver

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r3 · open · recovery identified the irreducible boundary as executable charged code plus correctness and two uniform cost bounds; no smaller cited library theorem supplies it.
* r2 · open · checked the contract, its project uses, and pinned Matroid/Computation sources; no executable polynomial matroid-intersection result supplies this contract.
* r1 · open · library search found no charged matroid-intersection implementation; the cited polynomial pretest still needs code and a cost proof.
-/
