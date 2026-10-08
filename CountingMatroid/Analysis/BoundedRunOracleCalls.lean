import CountingMatroid.Analysis.PrimitiveOracleCalls
import CountingMatroid.Model.Program

set_option autoImplicit false

/-!
# Oracle charges in one capped annealing run

The generic finite-loop charge lemma is proved. The run-level bound is open:
the state-independent primitive oracle bounds currently live in `ResourceBound`,
which imports the parent of this module. A standalone Lean probe verified that
the fourteen oracle-accounting declarations identified below elaborate unchanged
with only `Model.Program` imported. Moving them to an independent module would
make them available here without an import cycle. That move also edits
`ResourceBound`, outside this file's assigned ownership.
-/

namespace CountingMatroid.Analysis.BoundedRunOracleCalls

open CountingMatroid.Model
open CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines

/-- INTERNAL: Uniform oracle charges add across a finite charged loop. -/
theorem oracleCalls_repeatFor_le {β : Type}
    {f : ℕ → β → Arlib.Computation.Charged Op Cell β} {k : ℕ}
    (h : ∀ j b, oracleCalls (f j b) ≤ k) (n : ℕ) (b : β) :
    oracleCalls (Arlib.Computation.Charged.repeatFor f n b) ≤ n * k := by
  have hfold : ∀ (l : List ℕ) (b : β),
      oracleCalls (Arlib.Computation.Charged.foldl (fun b j => f j b) l b) ≤
        l.length * k := by
    intro l
    induction l with
    | nil => intro b; simp [oracleCalls]
    | cons j js ih =>
        intro b
        have htail := ih (f j b).val
        have hhead := h j b
        simp only [List.length_cons]
        calc
          oracleCalls (Arlib.Computation.Charged.foldl
              (fun b j => f j b) (j :: js) b) =
              oracleCalls (f j b) +
                oracleCalls (Arlib.Computation.Charged.foldl
                  (fun b j => f j b) js (f j b).val) := by
                simp [oracleCalls, Pi.add_apply, Nat.add_assoc, Nat.add_left_comm]
          _ ≤ k + js.length * k := Nat.add_le_add hhead htail
          _ = (js.length + 1) * k := by ring
  simpa [Arlib.Computation.Charged.repeatFor] using hfold (List.range n) b

/-- INTERNAL: Oracle calls of a bounded run obey a schedule-field polynomial,
independently of rational encoding lengths and output size.
TEXLINE: main.tex:1333-1346,1428-1439 -/
theorem boundedRun_oracleCalls_envelope :
    ∀ (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
      (s : AnnealingSchedule),
      let size := n + s.L + s.τ + s.restartCap + s.observations +
        s.drawTrials + binaryRatLength s.ρ + 1
      oracleCalls (CountingMatroid.Program.boundedRun r o₁ o₂ tape s 0) ≤
        100 * size ^ 100 := by
  intro n r o₁ o₂ tape s
  -- BLOCKER: ResourceBound's pairedRank_oracleCalls_le,
  -- weightOfKind_oracleCalls_le, recordObservation_oracleCalls_le, and
  -- boundedUniform_oracleCalls_zero are unavailable through imports:
  -- ResourceBound imports BoundedRunResourceEnvelope, which imports this file.
  -- Move those primitive lemmas into an upstream module, then combine
  -- state-independent chainStep, restartPhase, and observePhase query bounds
  -- through oracleCalls_repeatFor_le above.
  -- Verified extraction: move ResourceBound's oracleCalls_bind,
  -- oracleCalls_repeatFor_le, oracleCalls_foldl_le, greedyRank_oracleCalls_le,
  -- pairedProjections_oracleCalls_zero, pairedRank_oracleCalls_le,
  -- ratPower_oracleCalls_zero, weightOfKind_oracleCalls_le,
  -- classifyState_oracleCalls_zero, recordObservation_oracleCalls_le,
  -- boundedUniform_oracleCalls_zero, selectionVisit_oracleCalls_zero,
  -- selectPaired_oracleCalls_zero, and acceptance_oracleCalls_zero into
  -- Analysis/PrimitiveOracleCalls.lean, preserving their ResourceBound namespace.
  -- Import that module here and in ResourceBound, removing only the moved
  -- declarations from ResourceBound. No theorem statements need to change.
  -- The extraction probe imported Model.Program only and checked successfully;
  -- the four named primitive bounds have only the three ambient axioms.
  sorry

end CountingMatroid.Analysis.BoundedRunOracleCalls

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* recovery · blocked · verified the fourteen-declaration upstream extraction in Lean; completing the planned dependency move requires edits to ResourceBound, outside assigned ownership. No new proof debt introduced.
* r15 · open · separated oracle charges from rational-size invariants; direct boundedRun simplification leaves the nested phase charge, and the reusable primitive bounds are downstream in ResourceBound.
-/
