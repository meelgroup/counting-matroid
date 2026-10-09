import CountingMatroid.Analysis.ExchangeFlowEnergy
import CountingMatroid.Analysis.DefectTransportTwoPairs

set_option autoImplicit false

/-!
The recursive transport specialized to one ordered defect fiber and a
fixed two-pair transversal event, before applying goodness and the
three-pair coefficient inequality. Its remaining construction must route
balanced hole demands through the paper's leaf cliques. The case n = 2,
with no ordinary slots, is proved by its actual one-edge current. The
remaining n ≥ 3 construction needs the omitted-element quadratic signature
and the recursively conserved future-slot forms.
-/

namespace CountingMatroid.Analysis.DefectTransportRaw

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ExchangeFlowEnergy

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
    have hd : 0 < classMass π (.defect i k) := by
      dsimp only [π]
      rw [operational_class_mass, hdef ⟨i, k, hik⟩]
      exact_mod_cast div_pos (mul_pos (hw _)
        (DefectPartitionPositive.defect_partition_pos r o₁ o₂ q hq _)) hZ
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
    -- Concrete route: the product current J above has the exact divergence
    -- and is antisymmetric. Trying to make it a FlowCertificate leaves
    -- supported: κ state next = 0 → J state next = 0. This fails for
    -- nonneighboring source/sink states (the n=3 example in the parent).
    -- STILL OPEN: replace J by the recursive balanced-hole assignment;
    -- use the omitted-element quadratic signature for its split bound,
    -- conserve future-slot forms, route within leaf cliques, and prove
    -- leaf edge disjointness and shared-vertex divergence cancellation.
    -- Then use v_t ≤ D(i,t) and rescale energy by 2n² times the normalizer.
    sorry
end CountingMatroid.Analysis.DefectTransportRaw


/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · partial · proved and used the n = 2 no-ordinary-slot transport via the actual singleton defect/event states and a supported unit-edge current; the surviving branch has n ≥ 3. Located the recursive construction at main.tex:493-709 and its specialization at 868-898. The first split still needs the omitted-rank-weight Hessian signature, absent from the project and pinned libraries; positivity and balanced demands alone do not supply it.
-/
