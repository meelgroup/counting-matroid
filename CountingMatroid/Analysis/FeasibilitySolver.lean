import CountingMatroid.Model.Subroutines

set_option autoImplicit false

namespace CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model

/-- INTERNAL: Bridge the counted common-base predicate to the size-`r`
common-independent-set predicate used by the cited intersection algorithm.
TEXLINE: main.tex:278-289 -/
theorem commonBaseCount_pos_iff_common_independent (n r : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (hr : CommonRank r M₁ M₂) :
    0 < commonBaseCount M₁ M₂ ↔
      ∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
  classical
  constructor
  · intro h
    obtain ⟨I, hI⟩ : (commonBases M₁ M₂).Nonempty := by
      simpa only [commonBaseCount, Finset.card_pos] using h
    have hB : M₁.IsBase (I : Set (Fin n)) ∧ M₂.IsBase (I : Set (Fin n)) := by
      simpa only [commonBases, Finset.mem_filter, Finset.mem_univ, true_and] using hI
    refine ⟨I, ?_, hB.1.indep, hB.2.indep⟩
    have hcard := hB.1.encard_eq_eRank
    simpa [hr.1] using hcard
  · rintro ⟨I, hcard, hI₁, hI₂⟩
    have hB₁ : M₁.IsBase (I : Set (Fin n)) := by
      apply hI₁.isBase_of_eRk_ge I.finite_toSet
      rw [hI₁.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, hr.1]
    have hB₂ : M₂.IsBase (I : Set (Fin n)) := by
      apply hI₂.isBase_of_eRk_ge I.finite_toSet
      rw [hI₂.eRk_eq_encard, Set.encard_coe_eq_coe_finsetCard, hcard, hr.2]
    apply Finset.card_pos.mpr
    exact ⟨I, by simpa [commonBases] using And.intro hB₁ hB₂⟩

/-- PAPER: main.tex:283-289
BORROWED: Schrijver2003, Section 41.2, Theorem 41.4.
The cited polynomial matroid-intersection pretest must be implemented on the
project's charged oracle interface, with correctness and uniform cost bounds. -/
theorem exists_feasibility_contract : Nonempty FeasibilityContract := by
  classical
  suffices h : ∃ (solver : FeasibilityImplementation)
      (callConstant callDegree bitConstant bitDegree : ℕ),
      (∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (o₁ o₂ : IndependenceOracle n),
        FullGround M₁ M₂ → CommonRank r M₁ M₂ →
        ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
        (solver.run n r o₁ o₂).val = decide
          (∃ I : Finset (Fin n), I.card = r ∧
            M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)))) ∧
      FeasibilityBounded solver callConstant callDegree bitConstant bitDegree by
    obtain ⟨solver, callConstant, callDegree, bitConstant, bitDegree,
      hcorrect, hbounded⟩ := h
    refine ⟨⟨solver, callConstant, callDegree, bitConstant, bitDegree, ?_, hbounded⟩⟩
    intro n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
    rw [hcorrect n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂]
    exact Bool.decide_congr
      (commonBaseCount_pos_iff_common_independent n r M₁ M₂ hr).symm
  -- BLOCKER: construct an actual charged implementation of the cited
  -- matroid-intersection test on the two n-bit oracles, and prove its
  -- size-r independent-set answer and uniform polynomial bounds for
  -- `oracleCalls` and `otherSteps` on that same implementation.
  -- The bridge from that decision to the required common-base answer is
  -- proved above; no executable polynomial solver is installed here.
  -- Enumerating candidate `Finset (Fin n)`s gives a decision procedure,
  -- but has exponentially many oracle queries and cannot establish
  -- `FeasibilityBounded`.
  sorry

end CountingMatroid.Analysis.FeasibilitySolver

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r5 · open · searched pinned Mathlib and Arlib for matroid-intersection code; none supplies a charged polynomial pretest, while exhaustive candidate enumeration has exponential oracle cost.
* r4 · decomposed · proved the common-base/size-r-independent bridge and narrowed the remaining executable solver obligation to the predicate in Schrijver's cited pretest.
* r3 · open · recovery identified the irreducible boundary as executable charged code plus correctness and two uniform cost bounds; no smaller cited library theorem supplies it.
* r2 · open · checked the contract, its project uses, and pinned Matroid/Computation sources; no executable polynomial matroid-intersection result supplies this contract.
* r1 · open · library search found no charged matroid-intersection implementation; the cited polynomial pretest still needs code and a cost proof.
-/
