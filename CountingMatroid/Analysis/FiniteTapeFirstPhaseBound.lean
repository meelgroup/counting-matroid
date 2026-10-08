import CountingMatroid.Analysis.FirstPhaseFailure

set_option autoImplicit false

/-!
Normalize the finite-tape first-certificate-failure estimate to a finite
counting inequality. The live handoff of the probability estimate was
rejected, so this module asserts only the proved normalization; the estimate
itself remains inside `FiniteTapeLowerTail.finite_tape_lower_tail_bound`.
-/

namespace CountingMatroid.Analysis.FiniteTapeFirstPhaseBound

open CountingMatroid.Model

/-- INTERNAL: Normalize the desired first-certificate-failure mass bound to
an inequality with denominator cleared. This does not assert a probability
estimate or require any matroid promise.
TEXLINE: main.tex:1207-1285,1392-1427 -/
theorem finite_tape_first_phase_failure_iff (n r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (p : InputParams) (j : ℕ) :
    let s := CountingMatroid.Interface.Pseudocode.setup n p
    let m := CountingMatroid.Model.Run.blockLength n r p
    let bad := {bits : List Bool | bits.length = m ∧
      FirstPhaseFailure.FirstFailure r o₁ o₂
        (fun i => (bits[i]?).getD false) s j}
    ((bad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m ≤
      1 / (8 * ((s.L : ENNReal) + 1))) ↔
    (bad.ncard : ENNReal) * (1 / 2 : ENNReal) ^ m *
      (8 * ((s.L : ENNReal) + 1)) ≤ 1 := by
  dsimp only
  exact ENNReal.le_div_iff_mul_le
    (Or.inr (by norm_num : (1 : ENNReal) ≠ 0))
    (Or.inr (by norm_num : (1 : ENNReal) ≠ ⊤))

end CountingMatroid.Analysis.FiniteTapeFirstPhaseBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r18 · rejected handoff · `r18-lower-tail-first-phase-1` received `mechanical admission rejected; retain all files` with no further diagnostic. Replaced the unproved exported budget with its proved denominator-clearing equivalence; the probability obligation remains in the assigned parent.
* r18 · open · attempted finite-cardinality normalization of the first-certificate-failure event; the conditional fresh-suffix law, restart mean, stationary-mean MSE, and adaptive finite-tape coupling remain to be proved. The lower-tail parent uses this precise per-phase boundary via the proved certificate cover and union bound.
-/
