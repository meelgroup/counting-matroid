import CountingMatroid.Analysis.SingleRunAccuracy
import CountingMatroid.Analysis.IndependentRunsCore
import CountingMatroid.Analysis.MedianBadMajority
import CountingMatroid.Analysis.IndependentRunsTail
import CountingMatroid.Analysis.ScheduleConfidence

set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Mapping each fresh block commutes with recursive independent sampling. -/
theorem fairBlocks_map (m length : ℕ) (f : List Bool → ℚ) :
    (CountingMatroid.Model.Run.fairBlocks m length).map (List.map f) =
      independentRuns ((CountingMatroid.Model.Run.fairTape length).map f) m := by
  induction m with
  | zero =>
      change (PMF.pure ([] : List (List Bool))).map (List.map f) = pure []
      exact PMF.pure_map _ _
  | succ m ih =>
      change (((CountingMatroid.Model.Run.fairTape length).bind fun b =>
        (CountingMatroid.Model.Run.fairBlocks m length).map (List.cons b))).map (List.map f) =
        ((CountingMatroid.Model.Run.fairTape length).map f).bind (fun x =>
          (independentRuns ((CountingMatroid.Model.Run.fairTape length).map f) m).map
            (List.cons x))
      simp only [PMF.map_bind, PMF.bind_map]
      congr 1
      funext b
      calc
        PMF.map (List.map f) (PMF.map (List.cons b)
            (CountingMatroid.Model.Run.fairBlocks m length)) =
          PMF.map (List.cons (f b))
            (PMF.map (List.map f) (CountingMatroid.Model.Run.fairBlocks m length)) := by
              rw [PMF.map_comp, PMF.map_comp]
              rfl
        _ = _ := by rw [ih]; rfl
/-- INTERNAL: Reading every valid list index reproduces a mapped list. -/
theorem range_map_getD {α β : Type} (l : List α) (d : α) (f : α → β) :
    (List.range l.length).map (fun j => f ((l[j]?).getD d)) = l.map f := by
  apply List.ext_getElem
  · simp
  · intro i hi₁ hi₂
    simp at hi₁ hi₂ ⊢
    rw [List.getElem?_eq_getElem hi₁]
    rfl
/-- INTERNAL: Every sampled block list has the requested number of blocks. -/
theorem fairBlocks_support_length (m length : ℕ) (blocks : List (List Bool))
    (h : blocks ∈ (CountingMatroid.Model.Run.fairBlocks m length).support) :
    blocks.length = m := by
  induction m generalizing blocks with
  | zero =>
      change blocks ∈ (PMF.pure ([] : List (List Bool))).support at h
      simpa using h
  | succ m ih =>
      change blocks ∈ ((CountingMatroid.Model.Run.fairTape length).bind fun block =>
        (CountingMatroid.Model.Run.fairBlocks m length).map (List.cons block)).support at h
      rw [PMF.mem_support_bind_iff] at h
      rcases h with ⟨block, hblock, hs⟩
      rw [PMF.mem_support_map_iff] at hs
      rcases hs with ⟨rest, hrest, heq⟩
      subst blocks
      simp [ih rest hrest]
/-- INTERNAL: A PMF pushforward depends only on values in its support. -/
theorem pmf_map_congr_support {α β : Type} (q : PMF α) (f g : α → β)
    (h : ∀ x ∈ q.support, f x = g x) : q.map f = q.map g := by
  classical
  apply PMF.ext
  intro y
  simp only [PMF.map_apply]
  apply tsum_congr
  intro x
  by_cases hx : x ∈ q.support
  · rw [h x hx]
  · have hz : q x = 0 := by simpa [PMF.mem_support_iff] using hx
    simp [hz]

/-- INTERNAL: After a negative pretest, the estimator law is the median of independent one-run outputs.
TEXLINE: main.tex:1442-1448 -/
theorem estimateLaw_eq_independentRuns (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n)
    (p : CountingMatroid.Model.InputParams)
    (hpretest : CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ = none) :
    CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p =
    (independentRuns
      ((CountingMatroid.Model.Run.fairTape (CountingMatroid.Model.Run.blockLength n r p)).map
        (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false) (CountingMatroid.Interface.Pseudocode.setup n p)))
      (CountingMatroid.Interface.Pseudocode.setup n p).repetitions).map
      CountingMatroid.Interface.Pseudocode.median := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let width := CountingMatroid.Model.Run.blockLength n r p
  let f : List Bool → ℚ := fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
          (fun i => (bits[i]?).getD false) s
  change (CountingMatroid.Model.Run.fairBlocks s.repetitions width).map
    (fun blocks => CountingMatroid.Interface.Pseudocode.estimate solver n r o₁ o₂ p
      (CountingMatroid.Model.Run.blockTape blocks)) = _
  simp only [CountingMatroid.Interface.Pseudocode.estimate, hpretest]
  have hmap : (CountingMatroid.Model.Run.fairBlocks s.repetitions width).map
      (fun blocks => CountingMatroid.Interface.Pseudocode.median
        ((List.range s.repetitions).map fun j =>
          CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
            (CountingMatroid.Model.Run.blockTape blocks j) s)) =
      (CountingMatroid.Model.Run.fairBlocks s.repetitions width).map
        (fun blocks => CountingMatroid.Interface.Pseudocode.median (blocks.map f)) := by
    apply pmf_map_congr_support
    intro blocks hb
    have hlen := fairBlocks_support_length s.repetitions width blocks hb
    rw [← hlen]
    congr 1
    exact range_map_getD blocks ([] : List Bool) f
  rw [hmap]
  calc
    (CountingMatroid.Model.Run.fairBlocks s.repetitions width).map
        (fun blocks => CountingMatroid.Interface.Pseudocode.median (blocks.map f)) =
      ((CountingMatroid.Model.Run.fairBlocks s.repetitions width).map (List.map f)).map
        CountingMatroid.Interface.Pseudocode.median := by rw [PMF.map_comp]; rfl
    _ = _ := by rw [fairBlocks_map]

/-- PAPER: main.tex:1442-1462
Independent bounded runs with one-run failure at most one quarter give the
requested confidence after the paper's scheduled median repetitions. -/
theorem median_amplification_bound (solver : FeasibilityImplementation)
    (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (p : InputParams)
    (lower upper : ℚ)
    (hpretest : CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ = none)
    (hrun :
      let s := CountingMatroid.Interface.Pseudocode.setup n p
      let runLaw :=
        (CountingMatroid.Model.Run.fairTape
          (CountingMatroid.Model.Run.blockLength n r p)).map
          (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
            (fun i => (bits[i]?).getD false) s)
      runLaw.toOuterMeasure {y : ℚ | y < lower ∨ upper < y} ≤
        (1 / 4 : ENNReal)) :
    (CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p).toOuterMeasure
      {y : ℚ | y < lower ∨ upper < y} ≤ ENNReal.ofReal (p.δ : ℝ) := by
  let s := CountingMatroid.Interface.Pseudocode.setup n p
  let q := (CountingMatroid.Model.Run.fairTape
      (CountingMatroid.Model.Run.blockLength n r p)).map
      (fun bits => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (fun i => (bits[i]?).getD false) s)
  let bad : ℚ → Bool := fun x => decide (x < lower ∨ upper < x)
  have hq : q.toOuterMeasure {x | bad x = true} ≤ (1 / 4 : ENNReal) := by
    simpa only [bad, decide_eq_true_eq] using hrun
  obtain ⟨hrep, hδ⟩ := schedule_confidence_bound n p
  have hodd : Odd (10 * s.bδ + 1) := ⟨5 * s.bδ, by omega⟩
  rw [estimateLaw_eq_independentRuns solver n r o₁ o₂ p hpretest,
    PMF.toOuterMeasure_map_apply]
  change (independentRuns q s.repetitions).toOuterMeasure
    (CountingMatroid.Interface.Pseudocode.median ⁻¹'
      {y : ℚ | y < lower ∨ upper < y}) ≤ ENNReal.ofReal (p.δ : ℝ)
  rw [hrep]
  have hsubset :
      (CountingMatroid.Interface.Pseudocode.median ⁻¹'
        {y : ℚ | y < lower ∨ upper < y}) ∩
      (independentRuns q (10 * s.bδ + 1)).support ⊆
      {xs : List ℚ | (10 * s.bδ + 1) / 2 + 1 ≤ xs.countP bad} := by
    intro xs hx
    rcases hx with ⟨hbadxs, hsupp⟩
    have hlen := independentRuns_support_length q (10 * s.bδ + 1) xs hsupp
    have hoddxs : Odd xs.length := by rw [hlen]; exact hodd
    simpa [bad, hlen] using
      (median_bad_implies_majority_bad xs lower upper hoddxs hbadxs)
  calc
    (independentRuns q (10 * s.bδ + 1)).toOuterMeasure
        (CountingMatroid.Interface.Pseudocode.median ⁻¹'
          {y : ℚ | y < lower ∨ upper < y}) ≤
      (independentRuns q (10 * s.bδ + 1)).toOuterMeasure
        {xs : List ℚ | (10 * s.bδ + 1) / 2 + 1 ≤ xs.countP bad} :=
          (independentRuns q (10 * s.bδ + 1)).toOuterMeasure_mono hsubset
    _ ≤ (1 / 2 : ENNReal) ^ s.bδ := independent_runs_majority_tail q bad s.bδ hq
    _ ≤ ENNReal.ofReal (p.δ : ℝ) := hδ

end CountingMatroid.Analysis.MedianAmplification

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-07 · partial · proved the median majority bridge and support-length bridge;
  finite-product tail and charged halving threshold remain in imported children.
-/
