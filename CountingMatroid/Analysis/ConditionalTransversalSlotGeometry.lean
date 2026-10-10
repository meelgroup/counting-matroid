import CountingMatroid.Analysis.ConditionalDefectCoefficients
import CountingMatroid.Analysis.SlotDemandPairing

set_option autoImplicit false

/-!
The singleton-slot configuration for a conditional transversal split.
Fixed labels encode the assignment; the remaining pairs other than the
branching pair are ordinary slots.
-/

namespace CountingMatroid.Analysis.ConditionalTransversalSlotGeometry

open CountingMatroid.Model CountingMatroid.Program
open Classical
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.DefectSlotSplitSignature
open CountingMatroid.Analysis.SlotDemandPairing

/-- INTERNAL: The selected labels prescribed by the partial assignment.
TEXLINE: main.tex:810-815 -/
noncomputable def fixedLabels {n : ℕ} (σ : Assignment n) : PairedSet n := by
  classical
  exact Finset.univ.filter (fun e => σ e.1 = some e.2)

/-- INTERNAL: The ordinary slots omit the branching pair and all assigned pairs.
TEXLINE: main.tex:810-815 -/
noncomputable def freePairs {n : ℕ} (σ : Assignment n) (k : Fin n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun t => σ t = none ∧ t ≠ k)

/-- INTERNAL: The two labels of the branching pair are the root holes.
TEXLINE: main.tex:810-815 -/
def rootHoles {n : ℕ} (k : Fin n) : PairedSet n := {(k, false), (k, true)}

/-- INTERNAL: Membership in the fixed labels is exactly the assignment test.
TEXLINE: main.tex:810-815 -/
@[simp] theorem mem_fixed_labels {n : ℕ} (σ : Assignment n) (e : PairedGround n) :
    e ∈ fixedLabels σ ↔ σ e.1 = some e.2 := by
  classical
  simp [fixedLabels]

/-- INTERNAL: Membership in the ordinary slots is exactly the free-pair test.
TEXLINE: main.tex:810-815 -/
@[simp] theorem mem_free_pairs {n : ℕ} (σ : Assignment n) (k t : Fin n) :
    t ∈ freePairs σ k ↔ σ t = none ∧ t ≠ k := by
  classical
  simp [freePairs]

/-- INTERNAL: A completed root class is a transversal with the prescribed
branch bit; its other free bits are supplied by the completion.
TEXLINE: main.tex:810-817 -/
theorem root_completion_mem {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (c : Bool) (choices : Fin n → Bool) (i : Fin n) (b : Bool) :
    (i, b) ∈ fixedLabels σ ∪ (rootHoles k).erase (k, !c) ∪
      (freePairs σ k).image (fun t => (t, choices t)) ↔
      b = (if i = k then c else (σ i).getD (choices i)) := by
  classical
  have he : (rootHoles k).erase (k, !c) = {(k, c)} := by
    ext e
    rcases e with ⟨t, d⟩
    cases c <;> cases d <;> simp [rootHoles]
  rw [he]
  by_cases hik : i = k
  · subst i
    simp [hk, Finset.mem_image, Prod.mk.injEq]
  · cases hσ : σ i with
    | none => simp [Finset.mem_image, Prod.mk.injEq, hik, Ne.symm hik, hσ, eq_comm]
    | some a => simp [Finset.mem_image, Prod.mk.injEq, hik, Ne.symm hik, hσ, eq_comm]

/-- INTERNAL: Completion states at the two singleton root holes are exactly
the conditional transversal classes, with their original-subset encoding.
TEXLINE: main.tex:810-817 -/
theorem root_completion_iff {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (c : Bool) (state : PairedSet n) :
    SlotCompletion (fixedLabels σ) (rootHoles k) (freePairs σ k) (k, !c) state ↔
      ∃ A : Finset (Fin n),
        SubsetRespects (Function.update σ k (some c)) A ∧ state = transversalState A := by
  classical
  constructor
  · rintro ⟨choices, rfl⟩
    let bit := fun i => if i = k then c else (σ i).getD (choices i)
    let A := Finset.univ.filter (fun i => bit i = false)
    have hbit (i : Fin n) : decide (i ∉ A) = bit i := by
      cases h : bit i <;> simp [A, h]
    refine ⟨A, ?_, ?_⟩
    · intro i b hb
      rw [hbit]
      by_cases hik : i = k
      · subst i
        have hcb : c = b := by simpa using hb
        simpa [bit] using hcb
      · have hi : σ i = some b := by simpa [Function.update_of_ne hik] using hb
        simp [bit, hik, hi]
    · ext e
      rcases e with ⟨i, b⟩
      rw [root_completion_mem σ k hk]
      change b = bit i ↔ _
      cases h : bit i <;> cases b <;> simp [transversalState, A, h]
  · rintro ⟨A, hA, rfl⟩
    refine ⟨fun i => decide (i ∉ A), ?_⟩
    ext e
    rcases e with ⟨i, b⟩
    rw [root_completion_mem σ k hk]
    have hb : decide (i ∉ A) =
        (if i = k then c else (σ i).getD (decide (i ∉ A))) := by
      by_cases hik : i = k
      · subst i
        simpa using hA k c (by simp)
      · cases hi : σ i with
        | none => simp [hik]
        | some a =>
          have ha := hA i a (by simpa [Function.update_of_ne hik] using hi)
          simpa [hik] using ha
    rw [← hb]
    cases b <;> by_cases hi : i ∈ A <;> simp [transversalState, hi]

/-- INTERNAL: Original-subset transversal encoding is injective, as can be
read directly from the selected false labels.
TEXLINE: main.tex:270-281 -/
theorem transversal_encoding_injective {n : ℕ} :
    Function.Injective (transversalState (n := n)) := by
  intro A D h
  ext i
  have hi := congrArg (fun S : PairedSet n => (i, false) ∈ S) h
  simpa [transversalState] using hi

/-- INTERNAL: Reindex a root completion moment by the original subsets;
this bridge works for the weight alone or its product with any potential.
TEXLINE: main.tex:810-817 -/
theorem root_completion_moment {n : ℕ} (σ : Assignment n) (k : Fin n)
    (hk : σ k = none) (c : Bool) (f : PairedSet n → ℝ) :
    completionMoment (fixedLabels σ) (rootHoles k) (freePairs σ k) (k, !c) f =
      ∑ A : Finset (Fin n),
        if SubsetRespects (Function.update σ k (some c)) A then f (transversalState A) else 0 := by
  classical
  unfold completionMoment
  rw [← Finset.sum_filter, ← Finset.sum_filter]
  symm
  apply Finset.sum_bij (fun A _ => transversalState A)
  · intro A hA
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hA ⊢
    exact (root_completion_iff σ k hk c _).mpr ⟨A, hA, rfl⟩
  · intro A _ D _ h
    exact transversal_encoding_injective h
  · intro state hs
    have hs' := (Finset.mem_filter.mp hs).2
    obtain ⟨A, hA, he⟩ := (root_completion_iff σ k hk c state).mp hs'
    exact ⟨A, by simp [hA], he.symm⟩
  · intro A _
    rfl

/-- INTERNAL: The singleton root's unmultiplied totals are exactly the two
conditional transversal totals used by the target theorem.
TEXLINE: main.tex:810-817 -/
theorem root_slot_total {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (k : Fin n) (hk : σ k = none) (c : Bool) :
    slotTotal r o₁ o₂ q (fixedLabels σ) (rootHoles k) (freePairs σ k) (k, !c) =
      (transversalTotal r o₁ o₂ q (Function.update σ k (some c)) : ℝ) := by
  change completionMoment (fixedLabels σ) (rootHoles k) (freePairs σ k) (k, !c)
    (fun state => ((q ^ (n - (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ)) = _
  rw [root_completion_moment σ k hk]
  simp only [transversalTotal, transversalDeficiency, Rat.cast_sum, apply_ite, Rat.cast_zero]

end CountingMatroid.Analysis.ConditionalTransversalSlotGeometry
