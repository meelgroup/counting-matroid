import CountingMatroid.Model.Subroutines

set_option autoImplicit false

namespace CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines

/-- PAPER: main.tex:283-289
BORROWED: Schrijver2003, Section 41.2, Theorem 41.4.
The cited polynomial matroid-intersection pretest must be implemented on the
project's charged oracle interface, with correctness and uniform cost bounds. -/
theorem exists_feasibility_contract : Nonempty FeasibilityContract := by
  -- BLOCKER: no charged matroid-intersection implementation is available in
  -- this project, pinned Mathlib, or Arlib. In particular, there is no
  -- implementation with proofs of `FeasibilityCorrect` and `FeasibilityBounded`.
  sorry

end CountingMatroid.Analysis.FeasibilitySolver

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r2 · open · checked the contract, its project uses, and pinned Matroid/Computation sources; no executable polynomial matroid-intersection result supplies this contract.
* r1 · open · library search found no charged matroid-intersection implementation; the cited polynomial pretest still needs code and a cost proof.
-/
