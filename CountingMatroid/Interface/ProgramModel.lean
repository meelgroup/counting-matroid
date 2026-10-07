import CountingMatroid.Model.Program
import CountingMatroid.Interface.Pseudocode
import CountingMatroid.Interface.Encoding
import CountingMatroid.Model.Prior
import CountingMatroid.Model.Prelude
import CountingMatroid.Model.Operations
import CountingMatroid.Model.Subroutines
import CountingMatroid.Model.Run
import CountingMatroid.Analysis.SortedInsertValue

/-!
# The program and the model are the same algorithm

`CountingMatroid.Model.Program` is what the paper's claims are about: a charged
computation whose state is sealed and whose cost is an operator applied to it.
`CountingMatroid.Interface.Pseudocode` is the same algorithm as mathematics for the
answer/output object the correctness theorem measures. Time and space stay over
`CountingMatroid.Model.Program`; this file is only the transport for correctness.

It is a ladder. Each theorem below is proved from the ones above it, and
`outputLaw_answer_eq` is the top: it is the one lemma the analysis rewrites
through, and the only one anything outside this file should need.

The bridge is closed by a charged insertion lemma and the resulting median,
estimator, and PMF law equalities.
-/

set_option autoImplicit false

namespace CountingMatroid

/-- The pseudocode pretest is the value of the charged pretest. This is a definitional equality. -/
theorem pretest_value_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) : (CountingMatroid.Program.preprocess solver n r o₁ o₂).val = CountingMatroid.Interface.Pseudocode.pretest solver n r o₁ o₂ := by
  rfl

/-- Both sides use the same schedule, including its repetition count. This is a definitional equality. -/
theorem schedule_value_eq (n : ℕ) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Program.schedule n p).val = CountingMatroid.Interface.Pseudocode.setup n p := by
  rfl

/-- The pseudocode run reads the answer from the charged run. Its internal transition views are likewise defined by reading charged values, so this equality needs no separate transition induction. -/
theorem singleRun_answer_eq {n : ℕ} (r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (tape : ℕ → Bool) (s : CountingMatroid.Model.AnnealingSchedule) : (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0).val.1 = CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂ tape s := by
  rfl

/-- The charged estimator accumulates run answers by cons, while the pseudocode lists them in run order. Prove that the charged insertion sort computes the same median and that reversing the input does not change it. -/
theorem median_answer_eq (values : List ℚ) : (CountingMatroid.Program.medianRational values.reverse).val = CountingMatroid.Interface.Pseudocode.median values := by
  have hsort : ∀ (l : List ℚ) (acc : List ℚ), acc.Pairwise (· ≤ ·) →
      (Arlib.Computation.Charged.foldl
        (fun acc value => CountingMatroid.Program.sortedInsert value acc) l acc).val =
      l.foldl (fun acc value => acc.orderedInsert (· ≤ ·) value) acc := by
    intro l
    induction l with
    | nil => intro acc _; rfl
    | cons value rest ih =>
        intro acc hac
        have hac' : (acc.orderedInsert (· ≤ ·) value).Pairwise (· ≤ ·) :=
          List.Pairwise.orderedInsert (r := (· ≤ ·)) value acc hac
        simpa only [Arlib.Computation.Charged.val_foldl_cons, List.foldl_cons,
          CountingMatroid.Analysis.sortedInsert_value_eq value acc hac] using
          ih (acc.orderedInsert (· ≤ ·) value) hac'
  simp [CountingMatroid.Program.medianRational,
    CountingMatroid.Interface.Pseudocode.median, List.insertionSort,
    CountingMatroid.Model.Operations.nthRational,
    CountingMatroid.Model.Operations.halfNat]
  rw [hsort values.reverse [] List.Pairwise.nil, List.foldl_reverse]

/-- Unfold the charged binds, match the pretest branches, and identify each bounded-run answer. The median lemma handles the reversed list produced by charged cons operations. -/
theorem estimate_answer_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) (tape : ℕ → ℕ → Bool) : (CountingMatroid.Program.estimate solver n r o₁ o₂ p tape).val = CountingMatroid.Interface.Pseudocode.estimate solver n r o₁ o₂ p tape := by
  have hfold : ∀ (s : CountingMatroid.Model.AnnealingSchedule)
      (indices : List ℕ) (acc : List ℚ),
      (Arlib.Computation.Charged.foldl
        (fun acc j => do
          let (value, _) ← CountingMatroid.Program.boundedRun r o₁ o₂ (tape j) s 0
          CountingMatroid.Model.Operations.consRational value acc)
        indices acc).val =
      (indices.map (fun j => CountingMatroid.Interface.Pseudocode.singleRun r o₁ o₂
        (tape j) s)).reverse ++ acc := by
    intro s indices
    induction indices with
    | nil => intro acc; simp
    | cons j js ih =>
        intro acc
        simp only [Arlib.Computation.Charged.val_foldl_cons]
        rw [ih]
        simp [Arlib.Computation.Charged.val_bind,
          CountingMatroid.Interface.Pseudocode.singleRun,
          CountingMatroid.Model.Operations.consRational]
  simp [CountingMatroid.Program.estimate, CountingMatroid.Interface.Pseudocode.estimate,
    pretest_value_eq]
  split
  · simp_all
  · simp_all [schedule_value_eq, Arlib.Computation.Charged.repeatFor,
      median_answer_eq]

/-- Both laws draw the same finite fair-bit blocks and use the same exhausted-block convention. Apply pointwise answer equality under that common PMF; no lazy-versus-up-front sampling lemma is needed here. -/
theorem algorithmLaw_answer_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Model.Run.algorithmLaw solver n r o₁ o₂ p).map Arlib.Computation.Charged.val = CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p := by
  unfold CountingMatroid.Model.Run.algorithmLaw CountingMatroid.Interface.Pseudocode.estimateLaw
  simp only [schedule_value_eq]
  change PMF.map Arlib.Computation.Charged.val
      (PMF.map (fun blocks => CountingMatroid.Program.estimate solver n r o₁ o₂ p
        (CountingMatroid.Model.Run.blockTape blocks))
        (CountingMatroid.Model.Run.fairBlocks
          (CountingMatroid.Interface.Pseudocode.setup n p).repetitions
          (CountingMatroid.Model.Run.blockLength n r p))) =
      PMF.map (fun blocks => CountingMatroid.Interface.Pseudocode.estimate solver n r o₁ o₂ p
        (CountingMatroid.Model.Run.blockTape blocks))
        (CountingMatroid.Model.Run.fairBlocks
          (CountingMatroid.Interface.Pseudocode.setup n p).repetitions
          (CountingMatroid.Model.Run.blockLength n r p))
  rw [PMF.map_comp]
  congr 1
  funext blocks
  exact estimate_answer_eq solver n r o₁ o₂ p (CountingMatroid.Model.Run.blockTape blocks)

/-- The paper's correctness event reads the first coordinate of `outputLaw`. Project that coordinate, then rewrite by the answer-law equality; the work counters remain outside this bridge. -/
theorem outputLaw_answer_eq (solver : CountingMatroid.Model.Subroutines.FeasibilityImplementation) (n r : ℕ) (o₁ o₂ : CountingMatroid.Model.IndependenceOracle n) (p : CountingMatroid.Model.InputParams) : (CountingMatroid.Model.Run.outputLaw solver n r o₁ o₂ p).map Prod.fst = CountingMatroid.Interface.Pseudocode.estimateLaw solver n r o₁ o₂ p := by
  simp [CountingMatroid.Model.Run.outputLaw]
  rw [PMF.monad_map_eq_map, PMF.map_comp]
  simpa only [Function.comp_def] using algorithmLaw_answer_eq solver n r o₁ o₂ p

end CountingMatroid

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r1 · proved · closed the answer-law bridge and its six preceding and following correspondences.
-/
