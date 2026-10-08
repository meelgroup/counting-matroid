import CountingMatroid.Analysis.BoundedRunPhase
import CountingMatroid.Analysis.RationalHeight

set_option autoImplicit false
namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

/-- INTERNAL: A successful phase grows every rational-size budget by at most
one phase increment; aborts preserve the invariant vacuously. This is a
value-only statement, independent of the charge paid to reach that value.
TEXLINE: main.tex:1356-1390 -/
theorem phase_preserves_size {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (hρ : 0 ≤ s.ρ)
    (j : ℕ) (hj : j < s.L) (acc : Option (AnnealingCursor n))
    (hacc : PhaseSizeInvariant (runSize n s) j acc) :
    PhaseSizeInvariant (runSize n s) (j + 1)
      (boundedRunPhase r o₁ o₂ tape s j acc).val := by
  cases acc with
  | none => simp [boundedRunPhase, PhaseSizeInvariant]
  | some current =>
      intro next hnext
      dsimp [boundedRunPhase] at hnext
      cases hstarted : (restartPhase r o₁ o₂ tape s current.tables j
        current.bitCursor).val with
      | none => simp [hstarted] at hnext
      | some started =>
          simp only [hstarted, Arlib.Computation.Charged.val_bind] at hnext
          cases hobserved : (observePhase r o₁ o₂ tape s
            (ratPower s.ρ j).val current.currentWeights started).val with
          | none => simp [hobserved] at hnext
          | some observed =>
              simp only [hobserved, Arlib.Computation.Charged.val_bind] at hnext
              cases hfinished : (finishPhase s j current.currentWeights observed).val with
              | none => simp [hfinished] at hnext
              | some finished =>
                  -- BLOCKER: successful finishPhase needs bounds on each updated
                  -- multiplier, the observation counts/height, and its ratio.
                  -- The already-proved observation and ratio bounds live in
                  -- BoundedRunResourceEnvelope, downstream of the consumer.
                  -- After their extraction, the new obligation is the nested
                  -- multiplierWrite scan: each visit adds at most the encoding
                  -- lengths of pZero and pDefect, even without a uniqueness proof.
                  simp only [hfinished, Arlib.Computation.Charged.val_bind] at hnext
                  sorry
end CountingMatroid.Analysis.BoundedRunPhase
