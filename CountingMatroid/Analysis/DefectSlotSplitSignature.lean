import CountingMatroid.Analysis.OmittedRankWeightPolynomial
import CountingMatroid.Analysis.SlotBlockSignature
import CountingMatroid.Analysis.OmittedSlotQuadratic
import CountingMatroid.Analysis.OmittedTutteNormalization
import CountingMatroid.Analysis.OmittedSlotCoefficientFormula

set_option autoImplicit false

/-!
The omitted-element quadratic input to the recursive slot transport. The
slot totals and old-hole matrix below follow main.tex:516-601. The numerical
split estimate and the real signature-to-orthogonal-nonpositivity implication
are proved. The explicit block matrix is assembled on the old holes and two
new coordinates. The dual-matroid omitted-label extraction is constructed;
its descendant, homogeneous degree, and exact normalization to the operational
omitted-rank polynomial are proved. Identifying the surviving omitted-label
patterns with the final Hessian completion totals remains open; no signature
or rank-weight inequality is assumed by the parent theorem.
-/

namespace CountingMatroid.Analysis.DefectSlotSplitSignature

open CountingMatroid.Model CountingMatroid.Program
open scoped BigOperators
open Classical

/-- INTERNAL: A completion of fixed selected labels and displayed holes,
with one chosen label in each remaining original pair.
TEXLINE: main.tex:516-543 -/
def SlotCompletion {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hole : PairedGround n) (state : PairedSet n) : Prop :=
  ∃ choices : Fin n → Bool,
    state = B ∪ R.erase hole ∪ U.image (fun t => (t, choices t))

/-- PAPER: main.tex:522-526
The unmultiplied weight total for a displayed hole at a recursion node. -/
noncomputable def slotTotal {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (hole : PairedGround n) : ℝ :=
  ∑ state : PairedSet n, if SlotCompletion B R U hole state then
    (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ)
  else 0

/-- INTERNAL: All completion totals are positive, using any fixed choice of
bits and the positivity of every operational rank weight.
TEXLINE: main.tex:522-543 -/
theorem slot_total_pos {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (B R : PairedSet n) (U : Finset (Fin n))
    (hole : PairedGround n) : 0 < slotTotal r o₁ o₂ q B R U hole := by
  classical
  let S := B ∪ R.erase hole ∪ U.image (fun t => (t, false))
  have hS : SlotCompletion B R U hole S := ⟨fun _ => false, rfl⟩
  let term := fun state : PairedSet n => if SlotCompletion B R U hole state then
    ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ)
    else 0
  have hpos : 0 < term S := by
    dsimp only [term]
    rw [if_pos hS]
    exact_mod_cast pow_pos hq _
  exact hpos.trans_le (Finset.single_le_sum (fun state _ => by
    dsimp only [term]
    split_ifs
    · exact_mod_cast (pow_pos hq _).le
    · exact le_rfl) (Finset.mem_univ S))

/-- INTERNAL: Slot completion predicates enforce the n-set cardinality
needed by the operational omitted-element polynomial.
TEXLINE: main.tex:516-526,584-593 -/
theorem slot_completion_card {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (hole : PairedGround n) (hhole : hole ∈ R) (state : PairedSet n)
    (hstate : SlotCompletion B R U hole state) : state.card = n := by
  classical
  obtain ⟨choices, rfl⟩ := hstate
  have hd₁ : Disjoint B (R.erase hole) := hBR.mono_right (Finset.erase_subset _ _)
  have hd₂ : Disjoint (B ∪ R.erase hole) (U.image (fun t => (t, choices t))) := by
    rw [Finset.disjoint_left]
    intro e he hf
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hf
    obtain ⟨hnB, hnR⟩ := hU t ht (choices t)
    rcases Finset.mem_union.mp he with hB | hR
    · exact hnB hB
    · exact hnR (Finset.mem_of_mem_erase hR)
  rw [Finset.card_union_of_disjoint hd₂, Finset.card_union_of_disjoint hd₁,
    Finset.card_erase_of_mem hhole,
    Finset.card_image_of_injective U (by intro i j h; exact congrArg Prod.fst h)]
  have hpos : 0 < R.card := Finset.card_pos.mpr ⟨hole, hhole⟩
  omega

/-- INTERNAL: The completion total is the sum of the corresponding
squarefree omitted-polynomial coefficients, with its cardinality checked.
TEXLINE: main.tex:584-601 -/
theorem slot_coefficient_sum {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (hole : PairedGround n) (hhole : hole ∈ R) :
    (∑ state : PairedSet n, if SlotCompletion B R U hole state then
      ((MvPolynomial.coeff (OmittedRankWeightPolynomial.omittedExponent state)
        (OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q) : ℚ) : ℝ)
      else 0) = slotTotal r o₁ o₂ q B R U hole := by
  classical
  unfold slotTotal
  apply Finset.sum_congr rfl
  intro state _
  by_cases hs : SlotCompletion B R U hole state
  · rw [if_pos hs, if_pos hs, OmittedRankWeightPolynomial.omitted_rank_coefficient,
      if_pos (slot_completion_card B R U hBR hU hsize hole hhole state hs)]
  · rw [if_neg hs, if_neg hs]

/-- PAPER: main.tex:571-579
The old-hole quadratic matrix: two distinct displayed holes are omitted,
the next pair is doubled, and all other remaining pairs are singly occupied.
Its diagonal is zero. -/
noncomputable def futureMatrix {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n)
    (i j : PairedGround n) : ℝ :=
  if i = j then 0 else
    ∑ state : PairedSet n,
      if (∃ choices : Fin n → Bool,
        state = B ∪ (R.erase i).erase j ∪ {(t, false), (t, true)} ∪
          (U.erase t).image (fun s => (s, choices s))) then
        (q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ)
      else 0

/-- PAPER: main.tex:584-625
For the actual operational rank weights, the extracted omitted-element
Hessian is nonpositive on the orthogonal complement of e_a+e_b. Its
old-old block is futureMatrix; the two mixed blocks are the opposite child
hole totals. This is the signature input, before the numerical split bound. -/
theorem slot_split_signature (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1)
    (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (t : Fin n) (ht : t ∈ U) :
    let sₐ := fun i => slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) i
    let sᵦ := fun i => slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) i
    let u := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false)
    ∀ (h : PairedGround n → ℝ) (x y : ℝ),
      (∑ i ∈ R, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0 →
      (∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j) +
        2 * x * (∑ i ∈ R, sᵦ i * h i) +
        2 * y * (∑ i ∈ R, sₐ i * h i) + 2 * u * x * y ≤ 0 := by
  classical
  intro sₐ sᵦ u h x y horth
  have hu : 0 < u := slot_total_pos r o₁ o₂ q hq B _ _ _
  let V : R → R → ℝ := fun i j => futureMatrix r o₁ o₂ q B R U t i j
  let a : R → ℝ := fun i => sₐ i
  let b : R → ℝ := fun i => sᵦ i
  have hsig : sigPos (SlotBlockSignature.slotBlockMatrix V a b u).toQuadraticForm' ≤ 1 := by
    let N := (DefectPartitionQuadraticExtraction.pairedMatroid M₁ M₂)✶
    let G := OmittedSlotQuadratic.omittedSlotQuadratic N q B R U t
    have hN : N.E = Set.univ := by
      simpa only [N, Matroid.dual_ground] using
        DefectPartitionQuadraticExtraction.paired_matroid_full_ground M₁ M₂ hfull
    have hdesc := OmittedSlotQuadratic.omitted_slot_descendant N q hq B R U t
    have hdegree := OmittedSlotQuadratic.omitted_slot_homogeneous
      N q B R U hBR hU hsize t ht
    have hentries : RankWeightQuadraticSignature.hessian G =
        SlotBlockSignature.slotBlockMatrix V a b u := by
      ext i j
      rw [RankWeightQuadraticSignature.hessian_coefficient]
      change ((MvPolynomial.coeff (Finsupp.single i 1 + Finsupp.single j 1)
        (OmittedSlotQuadratic.omittedSlotQuadratic N q B R U t) *
        (if i = j then 2 else 1) : ℚ) : ℝ) = _
      rw [OmittedTutteNormalization.normalized_omitted_slot
        r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq]
      rw [OmittedSlotCoefficientFormula.slot_quadratic_state_sum
        r o₁ o₂ q B R U hU t ht]
      -- STILL OPEN: the exact coefficient identity for this constructed
      -- omitted-label descendant. Its four blocks must be futureMatrix,
      -- the two opposite child slotTotals, and u (with zero diagonals).
      -- BUILD BLOCKER (2026-10-09): a later permitted rebuild failed in
      -- the concurrently edited RankWeightQuadraticSignature.lean:460:
      -- Unknown constant List.length_eq_zero.mp. Its .olean is absent, so
      -- further parent/probe elaboration cannot run until that dependency
      -- is repaired by its owner. Both new support modules were checked
      -- and built successfully before this independent dependency change.
      -- The descendant and degree-two obligations are now proved. What
      -- remains is the purely combinatorial equivalence between
      -- SlotOmissionPattern at single i 1 + single j 1 and the completion
      -- predicates in the four blocks (including impossibility of the
      -- diagonal patterns). The complete derivative/substitution calculus
      -- now reduces the coefficient to an explicit finite state sum.
      -- Normalization, oracle ranks, dual rank, and all extraction
      -- multiplicities are proved in the two imported support modules.
      -- The existing selected-triple extraction has type Fin 3 and uses
      -- selected labels; it cannot rewrite a coefficient indexed by R⊕Bool.
      -- This is a same-paper bridge, not a proposed Prior assumption.
      sorry
    rw [← hentries]
    exact RankWeightQuadraticSignature.branden_huh_quadratic_signature
      N hN q hq hqone G hdesc hdegree
  have hbalance : (∑ i : R, (a i + b i) * h i) + u * (x + y) = 0 := by
    change (∑ i : R, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0
    rw [Finset.sum_coe_sort R (fun i => (sₐ i + sᵦ i) * h i)]
    exact horth
  have hnonpos := SlotBlockSignature.slot_block_nonpositive V a b u hu hsig
    (fun i => h i) x y hbalance
  dsimp only [V, a, b] at hnonpos
  have hinner (i : PairedGround n) :
      (∑ j : R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j) =
      ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j :=
    Finset.sum_coe_sort R (fun j => futureMatrix r o₁ o₂ q B R U t i j * h i * h j)
  simp_rw [hinner] at hnonpos
  rw [Finset.sum_coe_sort R (fun i => ∑ j ∈ R,
      futureMatrix r o₁ o₂ q B R U t i j * h i * h j),
    Finset.sum_coe_sort R (fun i => sᵦ i * h i),
    Finset.sum_coe_sort R (fun i => sₐ i * h i)] at hnonpos
  exact hnonpos

/-- INTERNAL: The numerical completion-of-the-square step on a balanced
old-hole vector. It needs nonpositivity only on the indicated orthogonal
complement, rather than nonpositivity of the full quadratic.
TEXLINE: main.tex:605-625 -/
theorem split_bound_of_orthogonal_nonpositivity {α : Type*} [DecidableEq α]
    (R : Finset α) (sₐ sᵦ h : α → ℝ) (V : α → α → ℝ) (u : ℝ)
    (hu : 0 < u) (hbalance : ∑ i ∈ R, (sₐ i + sᵦ i) * h i = 0)
    (horth : ∀ x y : ℝ,
      (∑ i ∈ R, (sₐ i + sᵦ i) * h i) + u * (x + y) = 0 →
      (∑ i ∈ R, ∑ j ∈ R, V i j * h i * h j) +
        2 * x * (∑ i ∈ R, sᵦ i * h i) +
        2 * y * (∑ i ∈ R, sₐ i * h i) + 2 * u * x * y ≤ 0) :
    2 * (∑ i ∈ R, sₐ i * h i) ^ 2 / u ≤
      -(∑ i ∈ R, ∑ j ∈ R, V i j * h i * h j) := by
  let X := ∑ i ∈ R, sₐ i * h i
  have hsum : (∑ i ∈ R, sᵦ i * h i) = -X := by
    simp_rw [add_mul, Finset.sum_add_distrib] at hbalance
    dsimp only [X]
    linarith
  have htest := horth (-X / u) (X / u) (by rw [hbalance]; ring)
  rw [hsum] at htest
  have heq :
      (∑ i ∈ R, ∑ j ∈ R, V i j * h i * h j) + 2 * X ^ 2 / u =
      (∑ i ∈ R, ∑ j ∈ R, V i j * h i * h j) +
        2 * (-X / u) * -X + 2 * (X / u) * X + 2 * u * (-X / u) * (X / u) := by
    field_simp
    ring
  have hbound := heq.trans_le htest
  dsimp only [X] at hbound
  linarith

/-- INTERNAL: The split-control invariant consumed by the flow recursion.
All slot configurations retain their disjointness and size hypotheses.
TEXLINE: main.tex:531-625 -/
def SlotSplitControl (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ) : Prop :=
  ∀ (B R : PairedSet n) (U : Finset (Fin n)),
    Disjoint B R →
    (∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R) →
    B.card + R.card + U.card = n + 1 →
    ∀ t ∈ U, ∀ h : PairedGround n → ℝ,
    let sₐ := fun i => slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) i
    let sᵦ := fun i => slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) i
    let u := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false)
    (∑ i ∈ R, (sₐ i + sᵦ i) * h i) = 0 →
    2 * (∑ i ∈ R, sₐ i * h i) ^ 2 / u ≤
      -(∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U t i j * h i * h j)

/-- PAPER: main.tex:615-625
The extracted Hessian supplies the split bound at every recursion node. -/
theorem slot_split_control (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) : SlotSplitControl n r o₁ o₂ q := by
  intro B R U hBR hU hsize t ht h sₐ sᵦ u hbalance
  apply split_bound_of_orthogonal_nonpositivity R sₐ sᵦ h
    (futureMatrix r o₁ o₂ q B R U t) u
    (slot_total_pos r o₁ o₂ q hq B _ _ _) hbalance
  exact slot_split_signature n r M₁ M₂ o₁ o₂ q hfull hr h₁ h₂ hq hqone
    B R U hBR hU hsize t ht h

end CountingMatroid.Analysis.DefectSlotSplitSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial, dependency blocked · proved exact dual-Tutte normalization, paired rank n, complement dual-rank identity, extraction multiplicities, and the finite-state omitted-slot coefficient formula in two new support modules; the parent uses both and still needs omission-pattern/completion equivalence. Both targeted builds and the parent elaboration passed before a concurrent RankWeightQuadraticSignature edit removed its object and failed a later permitted rebuild at List.length_eq_zero.mp.
* 2026-10-09 · partial · proved the real signature-to-orthogonal-nonpositivity step and exact block-vector expansion in two support modules; the original open theorem now has only the explicit operational block-matrix sigPos bound open. Its all-slot omitted-polynomial descendant and coefficient extraction remain unavailable; no new open declaration or Prior assumption was introduced.
-/
