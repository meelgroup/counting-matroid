import CountingMatroid.Model.Subroutines
import CountingMatroid.Analysis.RankOneFeasibility
import CountingMatroid.Analysis.IntersectionAugmentation
import CountingMatroid.Analysis.IntersectionSearchCost

set_option autoImplicit false

/-!
The common-base predicate is connected to the paper's feasibility pretest.
Ranks zero and one are implemented and verified using the charged interface;
the rank-one implementation is the first augmentation from the empty set.
An explicit capped exchange-graph implementation handles arbitrary rank.
Its uniform cost certificate is proved. The parent now reduces correctness to
the augmentation-progress obligation in a separate child file, which remains
open. The parent proof has no open tactic goals but depends on that obligation.
-/

namespace CountingMatroid.Analysis.FeasibilitySolver

open CountingMatroid.Model.Subroutines
open CountingMatroid.Model
open scoped Classical

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

/-- INTERNAL: The empty set settles the feasibility pretest at rank zero.
TEXLINE: main.tex:283-289 -/
theorem commonBaseCount_pos_of_rank_zero (n : ℕ)
    (M₁ M₂ : Matroid (Fin n)) (hr : CommonRank 0 M₁ M₂) :
    0 < commonBaseCount M₁ M₂ := by
  apply (commonBaseCount_pos_iff_common_independent n 0 M₁ M₂ hr).2
  exact ⟨∅, Finset.card_empty, by simp, by simp⟩

/-- INTERNAL: A charged rank test handles the empty common independent set
before invoking a solver for positive rank.
TEXLINE: main.tex:283-289 -/
def rankZeroGuard (solver : FeasibilityImplementation) : FeasibilityImplementation where
  run n r o₁ o₂ := do
    let zero ← Operations.natEqual r 0
    if zero then pure true else solver.run n r o₁ o₂

/-- INTERNAL: Value equation for the charged rank-zero branch. -/
theorem rankZeroGuard_val (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    ((rankZeroGuard solver).run n r o₁ o₂).val =
      if r = 0 then true else (solver.run n r o₁ o₂).val := by
  by_cases hr : r = 0 <;> simp [rankZeroGuard, Operations.natEqual, hr]

/-- INTERNAL: The rank-zero guard makes no additional oracle queries. -/
theorem rankZeroGuard_oracleCalls (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    oracleCalls ((rankZeroGuard solver).run n r o₁ o₂) =
      if r = 0 then 0 else oracleCalls (solver.run n r o₁ o₂) := by
  by_cases hr : r = 0 <;>
    simp [rankZeroGuard, Operations.natEqual, oracleCalls, hr]

/-- INTERNAL: The charged rank-zero guard adds exactly one comparison. -/
theorem rankZeroGuard_otherSteps (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    otherSteps ((rankZeroGuard solver).run n r o₁ o₂) =
      1 + if r = 0 then 0 else otherSteps (solver.run n r o₁ o₂) := by
  by_cases hr : r = 0 <;>
    simp [rankZeroGuard, Operations.natEqual, otherSteps, hr,
      Arlib.Computation.Op.all, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- INTERNAL: Use the verified first augmentation when the requested rank is
one; leave larger ranks to the intersection solver.
TEXLINE: main.tex:283-289 -/
def rankOneGuard (solver : FeasibilityImplementation) : FeasibilityImplementation where
  run n r o₁ o₂ := do
    let one ← Operations.natEqual r 1
    if one then RankOneFeasibility.singletonScan o₁ o₂ else solver.run n r o₁ o₂

/-- INTERNAL: Value equation for dispatch to the verified singleton scan. -/
theorem rankOneGuard_val (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    ((rankOneGuard solver).run n r o₁ o₂).val =
      if r = 1 then (RankOneFeasibility.singletonScan o₁ o₂).val
      else (solver.run n r o₁ o₂).val := by
  by_cases hr : r = 1 <;> simp [rankOneGuard, Operations.natEqual, hr]

/-- INTERNAL: The rank-one guard adds no oracle calls beyond the selected
scan or fallback implementation. -/
theorem rankOneGuard_oracleCalls (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    oracleCalls ((rankOneGuard solver).run n r o₁ o₂) =
      if r = 1 then oracleCalls (RankOneFeasibility.singletonScan o₁ o₂)
      else oracleCalls (solver.run n r o₁ o₂) := by
  by_cases hr : r = 1 <;>
    simp [rankOneGuard, Operations.natEqual, oracleCalls, hr]

/-- INTERNAL: The rank-one guard adds one charged comparison to either branch. -/
theorem rankOneGuard_otherSteps (solver : FeasibilityImplementation) (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) :
    otherSteps ((rankOneGuard solver).run n r o₁ o₂) =
      1 + if r = 1 then otherSteps (RankOneFeasibility.singletonScan o₁ o₂)
      else otherSteps (solver.run n r o₁ o₂) := by
  by_cases hr : r = 1 <;>
    simp [rankOneGuard, Operations.natEqual, otherSteps, hr,
      Arlib.Computation.Op.all, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- INTERNAL: Absorb the singleton scan and its guard into uniform polynomial
coefficients. The bound holds for arbitrary oracle functions, so the guard
introduces no promise-dependent resource assumption. -/
theorem rankOneGuard_bounded (solver : FeasibilityImplementation)
    (callConstant callDegree bitConstant bitDegree : ℕ)
    (hbounded : FeasibilityBounded solver callConstant callDegree bitConstant bitDegree) :
    FeasibilityBounded (rankOneGuard solver)
      (callConstant + 2) (callDegree + 3) (bitConstant + 5) (bitDegree + 3) := by
  intro n r o₁ o₂
  rw [rankOneGuard_oracleCalls, rankOneGuard_otherSteps]
  have hsize : 1 ≤ n + r + 1 := by omega
  have hcallPow : (n + r + 1) ^ callDegree ≤ (n + r + 1) ^ (callDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hbitPow : (n + r + 1) ^ bitDegree ≤ (n + r + 1) ^ (bitDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hcallCube : (n + r + 1) ^ 3 ≤ (n + r + 1) ^ (callDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hbitCube : (n + r + 1) ^ 3 ≤ (n + r + 1) ^ (bitDegree + 3) :=
    pow_le_pow_right₀ hsize (by omega)
  have hlinear : n ≤ (n + r + 1) ^ 3 := by
    calc
      n ≤ n + r + 1 := by omega
      _ ≤ (n + r + 1) ^ 3 := by
        simpa only [pow_one] using
          (pow_le_pow_right₀ hsize (by decide : 1 ≤ 3))
  have hwork : n * (n * (n + 1) + 3) ≤ 4 * (n + r + 1) ^ 3 := by
    have hproduct : n * (n * (n + 1)) ≤
        (n + r + 1) * ((n + r + 1) * (n + r + 1)) :=
      Nat.mul_le_mul (by omega) (Nat.mul_le_mul (by omega) (by omega))
    nlinarith
  have hunit : 1 ≤ (n + r + 1) ^ (bitDegree + 3) := one_le_pow₀ hsize
  obtain ⟨hc, hb⟩ := hbounded n r o₁ o₂
  have hc' := hc.trans (Nat.mul_le_mul_left callConstant hcallPow)
  have hb' := hb.trans (Nat.mul_le_mul_left bitConstant hbitPow)
  by_cases hr : r = 1
  · simp only [if_pos hr]
    rw [(RankOneFeasibility.singletonScan_costs o₁ o₂).1,
      (RankOneFeasibility.singletonScan_costs o₁ o₂).2]
    constructor <;> nlinarith
  · simp only [if_neg hr]
    constructor <;> nlinarith

/-- INTERNAL: Iterating the concrete augmentation at most `r` times reaches
size `r` exactly when a size-`r` common independent set exists. The loop invariant
compares its cardinality with every common independent competitor.
TEXLINE: main.tex:283-289 -/
theorem intersectionSolver_correct (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) :
    (IntersectionSearch.intersectionSolver.run n r o₁ o₂).val = decide
      (∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n))) := by
  classical
  have hloop (l : List ℕ) (I : Finset (Fin n))
      (hI₁ : M₁.Indep (I : Set (Fin n))) (hI₂ : M₂.Indep (I : Set (Fin n))) :
      let result := (Arlib.Computation.Charged.foldl
        (fun I _ => IntersectionSearch.augmentOnce o₁ o₂ I) l I).val
      M₁.Indep (result : Set (Fin n)) ∧ M₂.Indep (result : Set (Fin n)) ∧
        I.card ≤ result.card ∧ result.card ≤ I.card + l.length ∧
        ∀ J : Finset (Fin n), M₁.Indep (J : Set (Fin n)) →
          M₂.Indep (J : Set (Fin n)) → min (I.card + l.length) J.card ≤ result.card := by
    induction l generalizing I with
    | nil =>
      simp only [Arlib.Computation.Charged.val_foldl_nil, List.length_nil, Nat.add_zero]
      exact ⟨hI₁, hI₂, le_rfl, le_rfl, fun J _ _ => min_le_left _ _⟩
    | cons j l ih =>
      simp only [Arlib.Computation.Charged.val_foldl_cons, List.length_cons]
      let next := (IntersectionSearch.augmentOnce o₁ o₂ I).val
      have hp := IntersectionAugmentation.augmentation_progress M₁ M₂ o₁ o₂
        hfull h₁ h₂ I hI₁ hI₂
      obtain ⟨hout₁, hout₂, hlower, hupper, hcompare⟩ := ih next hp.1 hp.2.1
      have hstep : I.card ≤ next.card ∧ next.card ≤ I.card + 1 := by
        rcases hp.2.2 with hincrease | ⟨hfixed, _⟩
        · change next.card = I.card + 1 at hincrease
          omega
        · change next = I at hfixed
          rw [hfixed]
          omega
      refine ⟨hout₁, hout₂, hstep.1.trans hlower, ?_, ?_⟩
      · calc
          _ ≤ next.card + l.length := hupper
          _ ≤ I.card + (l.length + 1) := by omega
      intro J hJ₁ hJ₂
      rcases hp.2.2 with hincrease | ⟨hfixed, hmax⟩
      · have hcomp := hcompare J hJ₁ hJ₂
        change next.card = I.card + 1 at hincrease
        have heq : I.card + (l.length + 1) = next.card + l.length := by omega
        simpa only [heq] using hcomp
      · change next = I at hfixed
        have hJ := hmax J hJ₁ hJ₂
        have hJnext : J.card ≤ next.card := by
          rw [hfixed]
          exact hJ
        exact (min_le_right _ _).trans (hJnext.trans hlower)
  let result := (Arlib.Computation.Charged.foldl
    (fun I _ => IntersectionSearch.augmentOnce o₁ o₂ I) (List.range r)
      (∅ : Finset (Fin n))).val
  have hresult := hloop (List.range r) ∅ (by simp) (by simp)
  change M₁.Indep (result : Set (Fin n)) ∧ M₂.Indep (result : Set (Fin n)) ∧
    0 ≤ result.card ∧ result.card ≤ 0 + (List.range r).length ∧
    (∀ J : Finset (Fin n), M₁.Indep (J : Set (Fin n)) →
      M₂.Indep (J : Set (Fin n)) → min (0 + (List.range r).length) J.card ≤ result.card)
    at hresult
  simp only [List.length_range, Nat.zero_add] at hresult
  have hiff : result.card = r ↔ ∃ I : Finset (Fin n), I.card = r ∧
      M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
    constructor
    · intro hcard
      exact ⟨result, hcard, hresult.1, hresult.2.1⟩
    · rintro ⟨J, hcard, hJ₁, hJ₂⟩
      have hlower := hresult.2.2.2.2 J hJ₁ hJ₂
      rw [hcard, min_self] at hlower
      exact Nat.le_antisymm hresult.2.2.2.1 hlower
  change (result.card == r) = _
  have hbool : (result.card == r) = true ↔
      ∃ I : Finset (Fin n), I.card = r ∧
        M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)) := by
    simpa only [beq_iff_eq] using hiff
  cases hvalue : (result.card == r) <;> simp_all

/-- PAPER: main.tex:283-289
BORROWED: Schrijver2003, Section 41.2, Theorem 41.4.
The concrete charged implementation and its uniform cost bounds are supplied.
Correctness still depends on the shortest-path augmentation-progress obligation. -/
theorem exists_feasibility_contract : Nonempty FeasibilityContract := by
  classical
  suffices h : ∃ (solver : FeasibilityImplementation)
      (callConstant callDegree bitConstant bitDegree : ℕ),
      (∀ (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
        (o₁ o₂ : IndependenceOracle n),
        1 < r → FullGround M₁ M₂ → CommonRank r M₁ M₂ →
        ExactOracle M₁ o₁ → ExactOracle M₂ o₂ →
        (solver.run n r o₁ o₂).val = decide
          (∃ I : Finset (Fin n), I.card = r ∧
            M₁.Indep (I : Set (Fin n)) ∧ M₂.Indep (I : Set (Fin n)))) ∧
      FeasibilityBounded solver callConstant callDegree bitConstant bitDegree by
    obtain ⟨solver, callConstant, callDegree, bitConstant, bitDegree,
      hcorrect, hbounded⟩ := h
    refine ⟨⟨rankZeroGuard (rankOneGuard solver), callConstant + 2, callDegree + 3,
      bitConstant + 6, bitDegree + 3, ?_, ?_⟩⟩
    · intro n r M₁ M₂ o₁ o₂ hfull hr h₁ h₂
      rw [rankZeroGuard_val]
      by_cases hr0 : r = 0
      · subst r
        simp [commonBaseCount_pos_of_rank_zero n M₁ M₂ hr]
      · rw [if_neg hr0, rankOneGuard_val]
        by_cases hr1 : r = 1
        · subst r
          rw [if_pos rfl, RankOneFeasibility.singletonScan_correct M₁ M₂ o₁ o₂ h₁ h₂]
          exact Bool.decide_congr
            (commonBaseCount_pos_iff_common_independent n 1 M₁ M₂ hr).symm
        · rw [if_neg hr1,
            hcorrect n r M₁ M₂ o₁ o₂ (by omega) hfull hr h₁ h₂]
          exact Bool.decide_congr
            (commonBaseCount_pos_iff_common_independent n r M₁ M₂ hr).symm
    · intro n r o₁ o₂
      rw [rankZeroGuard_oracleCalls, rankZeroGuard_otherSteps]
      have hpow : 1 ≤ (n + r + 1) ^ (bitDegree + 3) := one_le_pow₀ (by omega)
      obtain ⟨hc, hb⟩ :=
        rankOneGuard_bounded solver callConstant callDegree bitConstant bitDegree
          hbounded n r o₁ o₂
      by_cases hr0 : r = 0
      · simp only [if_pos hr0, Nat.add_zero]
        constructor
        · exact Nat.zero_le _
        · nlinarith
      · simp only [if_neg hr0]
        exact ⟨hc, by nlinarith⟩
  refine ⟨IntersectionSearch.intersectionSolver, 100000, 8, 100000, 8, ?_,
    IntersectionSearchCost.intersectionSolver_bounded⟩
  intro n r M₁ M₂ o₁ o₂ _ hfull _ h₁ h₂
  exact intersectionSolver_correct n r M₁ M₂ o₁ o₂ hfull h₁ h₂

end CountingMatroid.Analysis.FeasibilitySolver

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r17 · partial · proved the complementary-basis cardinality separator used by augmentation_progress; isolated the remaining no-path obligations as basis certificates for the computed reachable set. The single-child handoff was also mechanically rejected; all new files remain owned locally.

* r16 · partial · proved the explicit solver's unconditional polynomial resource certificate after the two-child handoff was mechanically rejected. Only augmentation_progress remains open; parent cardinality induction and contract assembly elaborate against that obligation.

* r15 · decomposed · constructed a charged capped exchange-graph/BFS implementation and reduced the parent to its independent augmentation-progress and uniform-cost certificates. Proved exact query/table specifications and the parent cardinality induction; the two child certificates remain open pending live handoff.

* r14 · partial · implemented and verified the first augmentation from the empty set as a charged singleton scan; proved exact correctness and unconditional costs, and wired its rank-one guard and polynomial bounds into the parent. The remaining witness requires correctness only for 1 < r; no new open helper or transferred proof debt.
* r13 · partial · implemented the charged rank-zero guard; proved its value, zero additional oracle cost, and one-comparison overhead. The parent now handles rank zero and absorbs the guard cost into its polynomial coefficient. The positive-rank intersection implementation and its uniform bounds remain open; no new unproved declarations.
* r12 · open · library-first search again found no deterministic two-oracle intersection solver with polynomial charged bounds; checked augmentation and direct-sum independence statements. Preserved the existing bridge and target, and proposed the explicitly cited Schrijver dependency for Prior review; no new proof debt introduced.
* r11 · open · searched pinned Mathlib and Arlib for common independent sets, intersection algorithms, augmenting paths, and submodular minimization; no matching solver was found. Checked the single-matroid augmentation signatures and the unconditional cost quantifiers; the existing charged implementation dependency remains unresolved.
* r10 · recovery · isolated the missing charged augmenting-path implementation and its two cost proofs; a mathematical decider or a prior theorem alone cannot instantiate this contract without charged code.
* r9 · open · searched pinned Mathlib and Arlib for a two-oracle intersection algorithm or submodular minimization route; only single-matroid augmentation is present. The remaining goal is the cited solver's charged implementation and both uniform polynomial bounds.
* r8 · open · rechecked the entire pinned Mathlib and Arlib sources by matroid-intersection, common-independent-set, and augmenting-path statements; no executable two-oracle solver or cost certificate matches `FeasibilityContract`. The Schrijver citation remains the missing borrowed dependency.
* r7 · open · searched the pinned Mathlib matroid sources and all Arlib Lean sources by matroid-intersection and augmentation statement shape; no two-oracle implementation or polynomial charged certificate exists. The cited Schrijver theorem supplies an external algorithmic result, but the custom charged realization remains a local obligation.
* r6 · open · rechecked the contract shape and pinned Matroid/Computation sources; Mathlib has single-matroid augmentation but no executable matroid-intersection pretest or polynomial charged cost certificate. The Schrijver result remains a Prior proposal.
* r5 · open · searched pinned Mathlib and Arlib for matroid-intersection code; none supplies a charged polynomial pretest, while exhaustive candidate enumeration has exponential oracle cost.
* r4 · decomposed · proved the common-base/size-r-independent bridge and narrowed the remaining executable solver obligation to the predicate in Schrijver's cited pretest.
* r3 · open · recovery identified the irreducible boundary as executable charged code plus correctness and two uniform cost bounds; no smaller cited library theorem supplies it.
* r2 · open · checked the contract, its project uses, and pinned Matroid/Computation sources; no executable polynomial matroid-intersection result supplies this contract.
* r1 · open · library search found no charged matroid-intersection implementation; the cited polynomial pretest still needs code and a cost proof.
-/
