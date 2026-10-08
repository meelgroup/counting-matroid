import CountingMatroid.Model.Program

set_option autoImplicit false

/-!
A definitional name for the body of the bounded-run phase loop and the
rational-size invariant used by its work proof. The phase code is identical
to the lambda in `Program.boundedRun`; it adds no algorithmic assumption.
-/

namespace CountingMatroid.Analysis.BoundedRunPhase
open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines CountingMatroid.Program

/-- INTERNAL: The input size used by the bounded-run work envelope.
TEXLINE: main.tex:1348-1440 -/
def runSize (n : ℕ) (s : AnnealingSchedule) : ℕ :=
  n + s.L + s.τ + s.restartCap + s.observations +
    s.drawTrials + binaryRatLength s.ρ + 1

/-- INTERNAL: Name the exact phase-loop body so value and work induction share it.
TEXLINE: main.tex:1163-1201,1348-1440 -/
def boundedRunPhase {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (j : ℕ)
    (current : Option (AnnealingCursor n)) :
    Arlib.Computation.Charged Op Cell (Option (AnnealingCursor n)) := do
match current with
| none => pure none
| some current =>
    let q ← ratPower s.ρ j
    let started ← restartPhase r o₁ o₂ tape s current.tables j
      current.bitCursor
    match started with
    | none => pure none
    | some started =>
        let observed ← observePhase r o₁ o₂ tape s q
          current.currentWeights started
        match observed with
        | none => pure none
        | some observed =>
            let finished ← finishPhase s j current.currentWeights observed
            match finished with
            | none => pure none
            | some (ratio, nextWeights) =>
                let product ← ratMul current.product ratio
                let next ← successor j
                let update ← lessThan next s.L
                if update then
                  let tables ← learnedWeightWrite current.tables next s.L
                    nextWeights
                  pure (some ⟨tables, nextWeights, product,
                    observed.bitCursor⟩)
                else pure (some ⟨current.tables, nextWeights, product,
                  observed.bitCursor⟩)

/-- INTERNAL: All stored and current multipliers and the accumulated ratio
product have length at most a phase-linear budget. The aborted state satisfies
this vacuously. This deliberately loose budget avoids needing each table entry
to be updated only once in the nested finish-phase scan.
TEXLINE: main.tex:1356-1390 -/
def PhaseSizeInvariant {n : ℕ} (S j : ℕ)
    (acc : Option (AnnealingCursor n)) : Prop :=
  ∀ current, acc = some current →
    (∀ index, binaryRatLength (current.currentWeights index) ≤ (j + 1) * S ^ 10) ∧
    (∀ phase index, binaryRatLength (current.tables phase index) ≤ (j + 1) * S ^ 10) ∧
    binaryRatLength current.product ≤ (j + 1) * S ^ 10

end CountingMatroid.Analysis.BoundedRunPhase
