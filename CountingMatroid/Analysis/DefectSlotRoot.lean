import CountingMatroid.Analysis.SlotTransportFlow
import CountingMatroid.Analysis.ConditionalVarianceTree

set_option autoImplicit false

/-!
Identify the root completion classes in the defect/event transport with
the executable classifier and prescribed transversal event. All totals
use the actual operational rank weights.
-/

namespace CountingMatroid.Analysis.DefectSlotRoot

open CountingMatroid.Model CountingMatroid.Program
open Classical
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandRecursion
open CountingMatroid.Analysis.SlotDemandPairing
open CountingMatroid.Analysis.SlotTransportFlow
open CountingMatroid.Analysis.TransversalEventMean
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ExchangeFlowEnergy
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ObservableVarianceDecomposition

/-- INTERNAL: Displaying both labels at the full pair and one label at
all other nonempty pairs is exactly the operational defect fiber.
TEXLINE: main.tex:875-892 -/
theorem defect_root_shape {n : ℕ} (index : DefectIndex n) (state : PairedSet n) :
    (∃ choices : Fin n → Bool,
      state = {(index.fullPair, false), (index.fullPair, true)} ∪
        ((Finset.univ.erase index.emptyPair).erase index.fullPair).image
          (fun t => (t, choices t))) ↔
      (classifyState state).val = .defect index.emptyPair index.fullPair := by
  classical
  constructor
  · rintro ⟨choices, rfl⟩
    have he : ({(index.fullPair, false), (index.fullPair, true)} : PairedSet n) ∪
        ((Finset.univ.erase index.emptyPair).erase index.fullPair).image
          (fun t => (t, choices t)) = defectCompletion (fun t => some (choices t)) index := by
      simp only [defectCompletion, Option.getD_some, Finset.union_comm]
    rw [he]
    exact defect_completion_classified _ _
  · intro hkind
    refine ⟨fun t => decide ((t, true) ∈ state), ?_⟩
    have he := OmittedRankWeightPolynomial.defect_is_completion state index hkind
    simpa only [defectCompletion, Option.getD_some, Finset.union_comm] using he.symm

/-- INTERNAL: The fixed full-pair label and the other root hole together
are the two labels of that pair.
TEXLINE: main.tex:875-885 -/
theorem defect_root_base {n : ℕ} (i k : Fin n) (hik : i ≠ k) (a b : Bool) :
    ({(k, !b)} : PairedSet n) ∪ ({(i, !a), (k, b)} : PairedSet n).erase (i, !a) =
      {(k, false), (k, true)} := by
  classical
  have hp : (i, !a) ≠ (k, b) := fun he => hik (congrArg Prod.fst he)
  rw [Finset.erase_insert (by simpa using hp)]
  cases b <;> simp [Finset.pair_comm]

/-- PAPER: main.tex:875-892
The source root hole has exactly all states of the ordered defect fiber. -/
theorem source_completion_iff {n : ℕ} (i k : Fin n) (hik : i ≠ k)
    (a b : Bool) (state : PairedSet n) :
    SlotCompletion {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (i, !a) state ↔
        (classifyState state).val = .defect i k := by
  unfold SlotCompletion
  rw [defect_root_base i k hik a b]
  exact defect_root_shape ⟨i, k, hik⟩ state

/-- INTERNAL: Recover a concrete original-subset representation of every
accepted transversal using the existing finite reindexing identity.
TEXLINE: main.tex:270-281,875-892 -/
theorem transversal_representation {n : ℕ} (state : PairedSet n)
    (hkind : (classifyState state).val = .transversal) :
    ∃ A : Finset (Fin n), state = TransversalPartition.transversalState A := by
  classical
  by_contra hn
  have hnone : ∀ A : Finset (Fin n), TransversalPartition.transversalState A ≠ state := by
    simpa only [not_exists, ne_eq, eq_comm] using hn
  have h := ConditionalVarianceTree.transversal_sum_reindex
    (fun S : PairedSet n => if S = state then (1 : ℝ) else 0)
  have hleft : (∑ S : PairedSet n, if (classifyState S).val = .transversal then
      (if S = state then (1 : ℝ) else 0) else 0) = 1 := by
    rw [Finset.sum_eq_single state]
    · simp [hkind]
    · intro S _ hS
      simp [hS]
    · simp
  rw [hleft] at h
  simp only [hnone, if_false, Finset.sum_const_zero] at h
  exact one_ne_zero h

/-- INTERNAL: A sink completion selects the event's two prescribed labels
and the chosen bit at each ordinary pair.
TEXLINE: main.tex:875-892 -/
theorem event_completion_membership {n : ℕ} (i k : Fin n) (hik : i ≠ k)
    (a b : Bool) (choices : Fin n → Bool) (t : Fin n) (c : Bool) :
    (t, c) ∈ ({(k, !b)} : PairedSet n) ∪
      ({(i, !a), (k, b)} : PairedSet n).erase (k, b) ∪
      ((Finset.univ.erase i).erase k).image (fun s => (s, choices s)) ↔
      c = (if t = i then !a else if t = k then !b else choices t) := by
  classical
  have hdp : (k, b) ≠ (i, !a) := fun he => hik (congrArg Prod.fst he).symm
  have he : ({(i, !a), (k, b)} : PairedSet n).erase (k, b) = {(i, !a)} := by
    rw [Finset.erase_insert_of_ne hdp.symm, Finset.erase_singleton]
    rfl
  rw [he]
  by_cases hti : t = i
  · subst t
    simp [Finset.mem_image, Prod.mk.injEq, hik, Ne.symm hik, eq_comm]
  · by_cases htk : t = k
    · subst t
      simp [Finset.mem_image, Prod.mk.injEq, hti, hik, Ne.symm hik, eq_comm]
    · simp [Finset.mem_image, Prod.mk.injEq, hti, Ne.symm hti, htk, Ne.symm htk, eq_comm]

/-- PAPER: main.tex:875-892
The sink root hole has exactly the prescribed two-pair transversal event. -/
theorem event_completion_iff {n : ℕ} (i k : Fin n) (hik : i ≠ k)
    (a b : Bool) (state : PairedSet n) :
    SlotCompletion {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (k, b) state ↔ state ∈ pairEvent i k a b := by
  classical
  constructor
  · rintro ⟨choices, rfl⟩
    let bit := fun t : Fin n => if t = i then !a else if t = k then !b else choices t
    let A := Finset.univ.filter (fun t => bit t = false)
    have hbit (t : Fin n) : decide (t ∉ A) = bit t := by
      cases h : bit t <;> simp [A, h]
    have heq : ({(k, !b)} : PairedSet n) ∪
        ({(i, !a), (k, b)} : PairedSet n).erase (k, b) ∪
        ((Finset.univ.erase i).erase k).image (fun t => (t, choices t)) =
          TransversalPartition.transversalState A := by
      ext ⟨t, c⟩
      rw [event_completion_membership i k hik a b choices t c]
      change c = bit t ↔ _
      simp only [TransversalPartition.transversalState, Finset.mem_image,
        Finset.mem_univ, true_and, Prod.mk.injEq, hbit]
      simp [eq_comm]
    have hclass := ConditionalVarianceTree.transversal_state_classified A
    have hi : decide ((i, false) ∈ TransversalPartition.transversalState A) = a := by
      simp only [TransversalPartition.transversalState, Finset.mem_image,
        Finset.mem_univ, true_and, Prod.mk.injEq, hbit]
      cases a <;> simp [bit]
    have hk : decide ((k, false) ∈ TransversalPartition.transversalState A) = b := by
      simp only [TransversalPartition.transversalState, Finset.mem_image,
        Finset.mem_univ, true_and, Prod.mk.injEq, hbit]
      cases b <;> simp [bit, Ne.symm hik]
    rw [heq]
    simp only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨hclass, hi, hk⟩
  · intro hs
    obtain ⟨hclass, hi, hk⟩ : (classifyState state).val = .transversal ∧
        decide ((i, false) ∈ state) = a ∧ decide ((k, false) ∈ state) = b := by
      simpa only [pairEvent, Finset.mem_filter, Finset.mem_univ, true_and] using hs
    obtain ⟨A, rfl⟩ := transversal_representation state hclass
    have hiA : decide (i ∈ A) = a := by simpa [TransversalPartition.transversalState] using hi
    have hkA : decide (k ∈ A) = b := by simpa [TransversalPartition.transversalState] using hk
    have hbitI : decide (i ∉ A) = !a := by rw [← hiA]; simp
    have hbitK : decide (k ∉ A) = !b := by rw [← hkA]; simp
    refine ⟨fun t => decide (t ∉ A), ?_⟩
    ext ⟨t, c⟩
    rw [event_completion_membership i k hik a b]
    by_cases hti : t = i
    · subst t
      simp [TransversalPartition.transversalState, hbitI, hiA, eq_comm]
    · by_cases htk : t = k
      · subst t
        simp [TransversalPartition.transversalState, hbitK, hkA, hti, eq_comm]
      · simp [TransversalPartition.transversalState, hti, htk, eq_comm]

/-- PAPER: main.tex:892-895
The source root total is the complete ordered defect partition sum. -/
theorem source_slot_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (i k : Fin n) (hik : i ≠ k) (a b : Bool) :
    slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (i, !a) =
        (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, hik⟩ : ℝ) := by
  classical
  simp only [slotTotal, source_completion_iff i k hik a b,
    FirstPhaseFailure.defectPartition, Rat.cast_sum, apply_ite, Rat.cast_zero]

/-- INTERNAL: Evaluate a completion moment on the weighted indicator of
one state, for the pointwise root-demand identity.
TEXLINE: main.tex:493-498,684-692 -/
private theorem completion_moment_indicator {n : ℕ} (B R : PairedSet n)
    (U : Finset (Fin n)) (hole : PairedGround n) (f : PairedSet n → ℝ)
    (state : PairedSet n) :
    completionMoment B R U hole (fun S => if S = state then f S else 0) =
      if SlotCompletion B R U hole state then f state else 0 := by
  classical
  unfold completionMoment
  rw [Finset.sum_eq_single state]
  · simp
  · intro S _ hS
    simp [hS]
  · simp

/-- PAPER: main.tex:892-895
The sink root total is the normalizer times the prescribed event mass. -/
theorem event_slot_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool) :
    slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (k, b) =
        (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
          eventMass (IdealExchangeChain.operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b) := by
  classical
  let Z : ℝ := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw).1
  calc
    _ = ∑ state ∈ pairEvent i k a b,
        ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ) := by
      simp only [slotTotal, event_completion_iff i k hik a b]
      rw [← Finset.sum_filter]
      simp
    _ = Z * eventMass (IdealExchangeChain.operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b) := by
      rw [eventMass, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro state hs
      have hclass : (classifyState state).val = .transversal :=
        (Finset.mem_filter.mp hs).2.1
      have hweight : StationaryMeanIdentities.stateWeight r o₁ o₂ q w state =
          q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
        simp [StationaryMeanIdentities.stateWeight, hclass, weightOfKind,
          Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value]
      change _ = Z * ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w state : ℝ) / Z)
      rw [hweight, mul_div_cancel₀ _ hZ.ne']

/-- PAPER: main.tex:493-498,875-895
The two-hole root demand is exactly the normalized defect source minus
the normalized prescribed-event sink used by the parent flow certificate. -/
theorem root_demand_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (i k : Fin n) (hik : i ≠ k) (a b : Bool)
    (hA : 0 < eventMass (operationalLaw r o₁ o₂ q w hq hw) (pairEvent i k a b)) :
    completionDemand r o₁ o₂ q {(k, !b)} ((Finset.univ.erase i).erase k)
      (twoHoleRoot r o₁ o₂ q {(k, !b)} ((Finset.univ.erase i).erase k) (i, !a) (k, b)) =
        conditionalMeanDemand (operationalLaw r o₁ o₂ q w hq hw) (.defect i k) (pairEvent i k a b) := by
  classical
  let Z : ℝ := (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ)
  let D : ℝ := (FirstPhaseFailure.defectPartition r o₁ o₂ q ⟨i, k, hik⟩ : ℝ)
  let π := operationalLaw r o₁ o₂ q w hq hw
  let A := pairEvent i k a b
  let f := fun state : PairedSet n =>
    ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ)
  obtain ⟨hZq, _, _, hdef⟩ :=
    StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw
  have hZ : 0 < Z := by dsimp only [Z]; exact_mod_cast hZq
  have hD : 0 < D := by
    dsimp only [D]
    rw [← source_slot_total r o₁ o₂ q i k hik a b]
    exact slot_total_pos r o₁ o₂ q hq _ _ _ _
  have hwi : (0 : ℝ) < (w ⟨i, k, hik⟩ : ℝ) := by exact_mod_cast hw ⟨i, k, hik⟩
  have hmass : classMass π (.defect i k) = (w ⟨i, k, hik⟩ : ℝ) * D / Z := by
    dsimp only [π]
    rw [operational_class_mass, hdef ⟨i, k, hik⟩]
    simp only [Rat.cast_div, Rat.cast_mul]
    rfl
  have hpd : (i, !a) ≠ (k, b) := fun he => hik (congrArg Prod.fst he)
  funext state
  have hsource :
      (1 / D) * (if (classifyState state).val = .defect i k then f state else 0) =
        (if (classifyState state).val = .defect i k then π state / classMass π (.defect i k) else 0) := by
    by_cases hs : (classifyState state).val = .defect i k
    · rw [if_pos hs, if_pos hs, hmass]
      have hweight : StationaryMeanIdentities.stateWeight r o₁ o₂ q w state =
          w ⟨i, k, hik⟩ * q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
        simp [StationaryMeanIdentities.stateWeight, hs, weightOfKind, hik,
          Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value,
          Model.Operations.multiplierRead, Model.Operations.ratMul]
      change (1 / D) * f state =
        ((StationaryMeanIdentities.stateWeight r o₁ o₂ q w state : ℝ) / Z) /
          ((w ⟨i, k, hik⟩ : ℝ) * D / Z)
      rw [hweight, Rat.cast_mul]
      change (1 / D) * f state = (((w ⟨i, k, hik⟩ : ℝ) * f state) / Z) /
        ((w ⟨i, k, hik⟩ : ℝ) * D / Z)
      field_simp [hD.ne', hZ.ne', hwi.ne']
    · simp only [if_neg hs, mul_zero]
  have hsink :
      (-1 / (Z * eventMass π A)) * (if state ∈ A then f state else 0) =
        -(if state ∈ A then π state / eventMass π A else 0) := by
    by_cases hs : state ∈ A
    · rw [if_pos hs, if_pos hs]
      have hclass : (classifyState state).val = .transversal := (Finset.mem_filter.mp hs).2.1
      have hweight : StationaryMeanIdentities.stateWeight r o₁ o₂ q w state =
          q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) := by
        simp [StationaryMeanIdentities.stateWeight, hclass, weightOfKind,
          Model.Operations.natSub, BoundedRunResourceEnvelope.ratPower_value]
      change (-1 / (Z * eventMass π A)) * f state =
        -((StationaryMeanIdentities.stateWeight r o₁ o₂ q w state : ℝ) / Z / eventMass π A)
      rw [hweight]
      change (-1 / (Z * eventMass π A)) * f state = -(f state / Z / eventMass π A)
      ring
    · simp only [if_neg hs, mul_zero, neg_zero]
  unfold completionDemand nodePairing
  change (∑ hole ∈ ({(i, !a), (k, b)} : PairedSet n),
    (if hole = (i, !a) then 1 / slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (i, !a)
     else if hole = (k, b) then -1 / slotTotal r o₁ o₂ q {(k, !b)} {(i, !a), (k, b)}
      ((Finset.univ.erase i).erase k) (k, b) else 0) *
    completionMoment {(k, !b)} {(i, !a), (k, b)} ((Finset.univ.erase i).erase k)
      hole (fun S => if S = state then f S else 0)) = _
  rw [Finset.sum_insert (by simpa using hpd), Finset.sum_singleton]
  simp only [ite_true, if_neg (Ne.symm hpd)]
  rw [completion_moment_indicator, completion_moment_indicator,
    source_completion_iff i k hik a b, event_completion_iff i k hik a b,
    source_slot_total r o₁ o₂ q i k hik a b,
    event_slot_total r o₁ o₂ q w hq hw i k hik a b]
  have heq := congrArg₂ (fun x y : ℝ => x + y) hsource hsink
  by_cases hs : (classifyState state).val = .defect i k <;>
    by_cases hm : state ∈ A
  all_goals simpa only [D, Z, π, A, conditionalMeanDemand, sub_eq_add_neg,
    hs, hm, if_true, if_false] using heq

end CountingMatroid.Analysis.DefectSlotRoot
