import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.DefectTransportTwoPairs
import CountingMatroid.Analysis.OmittedRankWeightPolynomial
import CountingMatroid.Analysis.DefectSlotSplitSignature

set_option autoImplicit false

/-!
The recursive transport specialized to one ordered defect fiber and a
fixed two-pair transversal event, before applying goodness and the
three-pair coefficient inequality. Its remaining construction must route
balanced hole demands through the paper's leaf cliques. The case n = 2,
with no ordinary slots, is proved by its actual one-edge current. The
remaining n ≥ 3 construction needs the omitted-element quadratic signature
and the recursively conserved future-slot forms. The signature input is
exposed independently in DefectSlotSplitSignature and semantically used
through SlotSplitControl. The operational omitted polynomial is now defined, and its squarefree coefficient sums are identified
with the defect totals used to initialize the source.
-/

namespace CountingMatroid.Analysis.DefectTransportRaw

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: The two new holes balance their children, have opposite
values, and contribute exactly the quadratic split cost.
TEXLINE: main.tex:531-567 -/
private theorem balanced_hole_split {α : Type*} [DecidableEq α]
    (R : Finset α) (sₐ sᵦ h : α → ℝ) (u : ℝ) (hu : 0 < u)
    (hbalance : ∑ i ∈ R, (sₐ i + sᵦ i) * h i = 0) :
    let X := ∑ i ∈ R, sₐ i * h i
    let Y := ∑ i ∈ R, sᵦ i * h i
    let hₐ := -X / u
    let hᵦ := -Y / u
    X + u * hₐ = 0 ∧ Y + u * hᵦ = 0 ∧ hₐ + hᵦ = 0 ∧
      u * hₐ ^ 2 + u * hᵦ ^ 2 = 2 * X ^ 2 / u := by
  intro X Y hₐ hᵦ
  have hXY : X + Y = 0 := by
    dsimp only [X, Y]
    simpa only [add_mul, Finset.sum_add_distrib] using hbalance
  have hY : Y = -X := by linarith
  have hsum : hₐ + hᵦ = 0 := by
    dsimp only [hₐ, hᵦ]
    rw [← add_div, ← neg_add, hXY]
    simp
  refine ⟨?_, ?_, hsum, ?_⟩
  · dsimp only [hₐ]
    rw [mul_div_cancel₀ _ hu.ne']
    ring
  · dsimp only [hᵦ]
    rw [mul_div_cancel₀ _ hu.ne']
    ring
  · dsimp only [hₐ, hᵦ]
    rw [hY]
    field_simp
    ring

/-- INTERNAL: Specialize the paper's slot transport to the defect/event
slots and bound the off-subgraph totals by full defect partition sums.
No goodness or defect-coefficient inequality is used in this bound.
TEXLINE: main.tex:493-709,868-898 -/
theorem defect_transport_raw (n r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (w : Multipliers n)
    (hn : 0 < n) (hfull : FullGround M₁ M₂) (hr : CommonRank r M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂)
    (hq : 0 < q) (hqone : q ≤ 1) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    let π := operationalLaw r o₁ o₂ q w hq hw
    let κ := fun state next : PairedSet n =>
      exchangeProposal n hn state next * min (π state) (π next)
    let D := FirstPhaseFailure.defectPartition r o₁ o₂ q
    ∃ flow : FlowCertificate κ (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
      flowEnergy κ flow.current ≤ (2 * (n : ℝ) ^ 2) *
        (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
          (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
            ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
              (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) := by
  classical
  intro π κ D
  by_cases hn2 : n = 2
  · subst n
    obtain ⟨flow, hflow⟩ := DefectTransportTwoPairs.defect_transport_two_pairs
      r o₁ o₂ q w hn hq hw i k hik a b hA
    refine ⟨flow, hflow.trans ?_⟩
    have hslots : ∀ t : Fin 2, ¬ (t ≠ i ∧ t ≠ k) := by
      intro t h
      have hi : i.val ≠ k.val := fun he => hik (Fin.ext he)
      have hti : t.val ≠ i.val := fun he => h.1 (Fin.ext he)
      have htk : t.val ≠ k.val := fun he => h.2 (Fin.ext he)
      omega
    have hsum : (∑ t : Fin 2, if h : t ≠ i ∧ t ≠ k then
        (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro t _
      rw [dif_neg (hslots t)]
    rw [hsum]
    norm_num [π]
  ·
    have hn3 : 3 ≤ n := by
      have hi : i.val ≠ k.val := fun he => hik (Fin.ext he)
      omega
    let A := pairEvent i k a b
    obtain ⟨hZ, _, _, hdef⟩ :=
      StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
    have hDcoeff : D ⟨i, k, hik⟩ =
        ∑ state : PairedSet n,
          if ConditionalDefectCoefficients.Respects (fun _ => none) state ∧
              (classifyState state).val = .defect i k then
            MvPolynomial.coeff (OmittedRankWeightPolynomial.omittedExponent state)
              (OmittedRankWeightPolynomial.omittedRankPolynomial r o₁ o₂ q)
          else 0 := by
      rw [OmittedRankWeightPolynomial.defect_coefficient_sum
        r o₁ o₂ q (fun _ => none) ⟨i, k, hik⟩,
        ConditionalDefectCoefficients.defect_total_empty]
    have hDpos : 0 < D ⟨i, k, hik⟩ := by
      rw [hDcoeff]
      exact OmittedRankWeightPolynomial.defect_coefficient_total_pos
        r o₁ o₂ q hq (fun _ => none) ⟨i, k, hik⟩ rfl rfl
    have hd : 0 < classMass π (.defect i k) := by
      dsimp only [π]
      rw [operational_class_mass, hdef ⟨i, k, hik⟩]
      exact_mod_cast div_pos (mul_pos (hw _) hDpos) hZ
    let source := fun state : PairedSet n =>
      if (classifyState state).val = .defect i k then
        π state / classMass π (.defect i k) else 0
    let sink := fun state : PairedSet n =>
      if state ∈ A then π state / eventMass π A else 0
    have hsource : (∑ state, source state) = 1 := by
      have heq : (∑ state, source state) =
          classMass π (.defect i k) / classMass π (.defect i k) := by
        change _ = (∑ state, if (classifyState state).val = .defect i k then π state else 0) / _
        rw [Finset.sum_div]
        apply Finset.sum_congr rfl
        intro state _
        dsimp only [source]
        split_ifs <;> simp
      exact heq.trans (div_self hd.ne')
    have hsink : (∑ state, sink state) = 1 := by
      calc
        _ = ∑ state ∈ A, π state / eventMass π A := by
          dsimp only [sink]
          rw [← Finset.sum_filter]
          simp
        _ = eventMass π A / eventMass π A := by rw [← Finset.sum_div]; rfl
        _ = 1 := div_self hA.ne'
    let J := fun state next : PairedSet n =>
      source state * sink next - source next * sink state
    have hanti : ∀ state next, J state next = -J next state := by
      intro state next
      dsimp only [J]
      ring
    have hdiv : ∀ state,
        divergence J state = conditionalMeanDemand π (.defect i k) A state := by
      intro state
      simp only [divergence, J, Finset.sum_sub_distrib,
        ← Finset.mul_sum, ← Finset.sum_mul, hsource, hsink, mul_one, one_mul]
      rfl
    suffices hassembly :
        DefectSlotSplitSignature.SlotSplitControl n r o₁ o₂ q →
          ∃ flow : FlowCertificate κ
              (conditionalMeanDemand π (.defect i k) (pairEvent i k a b)),
            flowEnergy κ flow.current ≤ (2 * (n : ℝ) ^ 2) *
              (1 / classMass π (.defect i k) + 1 / eventMass π (pairEvent i k a b) +
                (2 / ((D ⟨i, k, hik⟩ : ℝ) * eventMass π (pairEvent i k a b))) *
                  ∑ t : Fin n, if h : t ≠ i ∧ t ≠ k then
                    (D ⟨i, t, Ne.symm h.1⟩ : ℝ) / (w ⟨t, k, h.2⟩ : ℝ) else 0) by
      exact hassembly (DefectSlotSplitSignature.slot_split_control n r M₁ M₂ o₁ o₂ q
        hfull hr h₁ h₂ hq hqone)
    intro hsplitControl
    -- INTERNAL: Realize the paper's new-hole values at every admissible
    -- node and bound their cost using the supplied all-node split control.
    have controlledSplit (B R : PairedSet n) (U : Finset (Fin n))
        (hBR : Disjoint B R)
        (hU : ∀ t ∈ U, ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
        (hsize : B.card + R.card + U.card = n + 1)
        (t : Fin n) (ht : t ∈ U) (h : PairedGround n → ℝ) :
        let sₐ := fun hole => DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, false) R) (U.erase t) hole
        let sᵦ := fun hole => DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, true) R) (U.erase t) hole
        let u := DefectSlotSplitSignature.slotTotal r o₁ o₂ q B
          (insert (t, false) R) (U.erase t) (t, false)
        (∑ hole ∈ R, (sₐ hole + sᵦ hole) * h hole) = 0 →
        ∃ hₐ hᵦ : ℝ,
          (∑ hole ∈ R, sₐ hole * h hole) + u * hₐ = 0 ∧
          (∑ hole ∈ R, sᵦ hole * h hole) + u * hᵦ = 0 ∧
          hₐ + hᵦ = 0 ∧
          u * hₐ ^ 2 + u * hᵦ ^ 2 ≤
            -(∑ hole ∈ R, ∑ other ∈ R,
              DefectSlotSplitSignature.futureMatrix r o₁ o₂ q B R U t hole other *
                h hole * h other) := by
      intro sₐ sᵦ u hbalance
      have hu : 0 < u := DefectSlotSplitSignature.slot_total_pos r o₁ o₂ q hq B _ _ _
      obtain ⟨hbalₐ, hbalᵦ, hopp, hcost⟩ := balanced_hole_split R sₐ sᵦ h u hu hbalance
      refine ⟨-(∑ hole ∈ R, sₐ hole * h hole) / u,
        -(∑ hole ∈ R, sᵦ hole * h hole) / u, hbalₐ, hbalᵦ, hopp, ?_⟩
      rw [hcost]
      exact hsplitControl B R U hBR hU hsize t ht h hbalance
    -- Concrete route: the product current J above has the exact divergence
    -- and is antisymmetric. Trying to make it a FlowCertificate leaves
    -- supported: κ state next = 0 → J state next = 0. This fails for
    -- nonneighboring source/sink states (the n=3 example in the parent).
    -- STILL OPEN: replace J by the recursive balanced-hole assignment;
    -- use hsplitControl for each node's split cost, conserve future-slot
    -- forms, iterate controlledSplit to assign leaf demands, route within
    -- leaf cliques, and prove
    -- leaf edge disjointness and shared-vertex divergence cancellation.
    -- Then use v_t ≤ D(i,t) and rescale energy by 2n² times the normalizer.
    sorry
end CountingMatroid.Analysis.DefectTransportRaw


/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · defined the operational omitted-element polynomial and proved its squarefree coefficient recovery, multiaffinity, and defect-total bridge; proved the numerical orthogonal-complement split bound, slot-completion coefficient bridge, and balanced new-hole equations with their exact cost. The parent now consumes the all-node SlotSplitControl invariant; its signature proof and recursive conservation/leaf-flow assembly remain open.
* 2026-10-09 · partial · proved and used the n = 2 no-ordinary-slot transport via the actual singleton defect/event states and a supported unit-edge current; the surviving branch has n ≥ 3. Located the recursive construction at main.tex:493-709 and its specialization at 868-898. The first split still needs the omitted-rank-weight Hessian signature, absent from the project and pinned libraries; positivity and balanced demands alone do not supply it.
-/
