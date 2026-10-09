import CountingMatroid.Analysis.BinaryRankWeightSignature
import CountingMatroid.Analysis.QuadraticSignatureHyperplane
import CountingMatroid.Analysis.LorentzianDirectionalSignature
import CountingMatroid.Analysis.RankWeightCoordinateLorentzian

set_option autoImplicit false

/-!
The original-variable mixed-derivative prerequisite for the rank-weight
signature theorem. Linear substitution and scalar closure are proved in the
parent's other support modules. The empty direction list is handled by
the two-element rank-weight calculation, and an identically zero direction
anywhere in the list gives the zero quadratic form. The remaining case,
where the list is nonempty and every direction is nonzero, now uses two
separate prerequisites: the matroid-specific coordinate Lorentzian certificate
in `RankWeightCoordinateLorentzian`, and the general nonnegative directional
signature consequence in `LorentzianDirectionalSignature`. Both support files
were released through a compiler-validated scheduler handoff; this module
does not supply their full proofs. Their basic degree/coefficient facts and
degree-two closure case are proved. The passage from a signature bound to a
hyperplane is proved by Mathlib diagonalization in
`QuadraticSignatureHyperplane`. The target proof contains no local hole,
but its full proof depends on both prerequisites; the pinned libraries contain
no applicable Lorentzian API.
-/

namespace CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

open scoped BigOperators
open QuadraticNonpositiveHyperplane

/-- INTERNAL: A zero direction anywhere in the mixed-derivative list
annihilates the polynomial, and all subsequent derivatives preserve zero.
TEXLINE: main.tex:340-343 -/
theorem mixed_derivatives_eq_zero_of_zero_mem {σ : Type} [Fintype σ]
    (ds : List (σ → ℚ)) (f : MvPolynomial σ ℚ)
    (hz : ∃ d ∈ ds, ∀ s, d s = 0) :
    ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) f = 0 := by
  induction ds with
  | nil => simp only [List.not_mem_nil, false_and, exists_false] at hz
  | cons d ds ih =>
    obtain ⟨e, he, hezero⟩ := hz
    rcases List.mem_cons.mp he with rfl | he
    · simp only [List.foldr_cons, hezero, map_zero, zero_mul, Finset.sum_const_zero]
    · rw [List.foldr_cons, ih ⟨e, he, hezero⟩]
      simp only [map_zero, mul_zero, Finset.sum_const_zero]

/-- PAPER: main.tex:334-348
The original-variable hyperplane consequence of the cited Lorentzian base
and closure results,
for the common matroid polynomial after exactly ground-size minus two
nonnegative directional derivatives. The fold is the parent's proved normal
form, with the last derivative at the head of the list.
BORROWED: Bränden–Huh, Lorentzian polynomials (2020), Theorems 4.10,
2.10 and Corollary 2.11 supply the Lorentzian base and closure input. -/
theorem mixed_directional_rank_weight_nonpositive_hyperplane {α : Type}
    [Fintype α] [DecidableEq α] (N : Matroid α) (hfull : N.E = Set.univ)
    (q : ℚ) (hq : 0 < q) (hqone : q ≤ 1)
    (ds : List (Option α → ℚ))
    (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s)
    (hlength : ds.length + 2 = Fintype.card α) :
    let p : MvPolynomial (Option α) ℚ := ∑ A : Finset α,
      MvPolynomial.C ((q ^ (N.eRk (A : Set α)).toNat)⁻¹) *
        MvPolynomial.X none ^ (Fintype.card α - A.card) *
          ∏ a ∈ A, MvPolynomial.X (some a)
    let g := ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p
    HasNonpositiveHyperplane (Matrix.toQuadraticForm' (fun i j =>
      ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j g)) : ℚ) : ℝ))) := by
  by_cases hz : ∃ d ∈ ds, ∀ s, d s = 0
  · dsimp only
    rw [mixed_derivatives_eq_zero_of_zero_mem ds _ hz]
    simp only [map_zero, Rat.cast_zero]
    refine ⟨0, ?_⟩
    intro v hv
    change Matrix.toLinearMap₂' ℝ (0 : Matrix (Option α) (Option α) ℝ) v v ≤ 0
    rw [map_zero]
    simp
  · cases ds with
    | nil =>
      exact BinaryRankWeightSignature.binary_tutte_nonpositive_hyperplane
        N q hq hqone (by simpa using hlength.symm)
    | cons d ds =>
      apply QuadraticSignatureHyperplane.hasNonpositiveHyperplane_of_sigPos_le_one
      -- The missing published inputs are now separate child obligations.
      -- The following comments preserve the pre-decomposition proof evidence.
      -- The linear-algebra implication is now proved: diagonalization
      -- deletes the sole positive square and transports its kernel back.
      -- The remaining goal is exactly sigPos of the displayed Hessian ≤ 1;
      -- it still needs the cited matroid-polynomial base/closure input.
      -- BLOCKER: library name not found. Statement-shape searches of pinned
      -- Mathlib and Arlib found no rank-weight polynomial Hessian bound,
      -- Lorentzian/complete-log-concavity invariant, or polynomial-stability
      -- closure supplying the common nonpositive hyperplane. Mathlib's
      -- quadratic signature API bounds dimension given a nonpositive subspace;
      -- it does not establish that subspace for these matroid coefficients.
      -- Arlib's local-to-global variance identities and PSD-order closure
      -- likewise do not provide the required matroid-polynomial input.
      -- Rechecked with hidden/ignored files included and package symlinks
      -- followed: Mathlib's matroid sources contain no Polynomial or
      -- MvPolynomial API; Arlib has no Matroid, MvPolynomial, pderiv or
      -- eRk declaration. No Lorentzian, complete-log-concavity, real-stable
      -- or hyperbolic-polynomial result was found in either library.
      -- Precisely missing are: Lorentzianity of the displayed T_{q,N},
      -- preservation by the nonnegative directional fold, and the quadratic
      -- Hessian implication giving HasNonpositiveHyperplane. The available
      -- QuadraticForm.sigPos_add_finrank_le_of_nonpos instead requires the
      -- nonpositive subspace as a hypothesis; it cannot supply this witness.
      -- The cited input is main.tex:334-348, BH2020 Theorems 4.10, 2.10
      -- and Corollary 2.11. Propose this exact consequence as prior input;
      -- no field of Prior has been added or assumed here.
      -- A stdin induction attempt failed on ds.length + 2 = |α|:
      -- this branch instead has ds.length + 3 = |α|, so the tail is cubic.
      -- Focused arithmetic probes also prove |α| ≠ 2 here, ruling out
      -- binary_tutte_nonpositive_hyperplane. Separate hyperplanes for the
      -- coordinate derivative Hessians cannot be added into a shared one.
      -- RankWeightQuadraticSignature imports and uses this theorem, so its
      -- general signature declaration cannot be imported as a proof of it.
      exact LorentzianDirectionalSignature.directional_hessian_sigPos_le_one _ _
        (RankWeightCoordinateLorentzian.rank_weight_coordinate_lorentzian
          N hfull q hq hqone) (d :: ds) hds hlength

end CountingMatroid.Analysis.MixedDirectionalRankWeightSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · validated parallel handoff · request agent5-coordinate-lorentzian-20261009-1 accepted at semantic-use stage; LorentzianDirectionalSignature and RankWeightCoordinateLorentzian transferred to scheduler ownership. The unchanged target has a complete proof body using both children; the mathematical proof debt is explicitly retained in their open base-certificate and directional-closure declarations.
* 2026-10-09 · decomposed · introduced the coordinate Lorentzian certificate and separated the matroid-specific certificate from general nonnegative directional closure. Proved the basic homogeneous-degree/coefficient invariants and the general degree-two closure case. The target uses both children; support exchange, higher-degree coordinate signatures, and general directional closure remain open for live OPEN handoff. No Prior field or assumption was added.
* 2026-10-09 · partial · proved QuadraticSignatureHyperplane.hasNonpositiveHyperplane_of_sigPos_le_one using Mathlib's weighted-square diagonalization and signature count; the nonempty branch now uses it. The remaining single hole is the at-most-one-positive Hessian signature bound from the cited Lorentzian base and closure input, absent from the pinned libraries. No assumption or open child lemma was added.
* 2026-10-09 · blocked · independently verified the borrowed-library blocker with symlink-following searches of all pinned Lean sources, including matroid/polynomial statement shapes and quadratic-signature APIs; no applicable base or closure input was found. Preserved every proof and the exact target, adding only diagnostic evidence; no new lemma, assumption, proof debt or import.
* 2026-10-09 · partial · proved mixed_derivatives_eq_zero_of_zero_mem and used it to close every list containing an identically zero direction, preserving the empty-list proof. Statement-shape searches including polynomial stability, complete log-concavity, quadratic signature and Arlib's local-to-global/PSD APIs found no applicable borrowed input. The nonempty all-nonzero case remains the same single proof hole; no assumption, child proof debt or import was added.
* 2026-10-09 · blocked · proved the identically zero head-direction branch; searched pinned Mathlib and Arlib by Lorentzian/log-concave closure, matroid polynomial Hessian and positive signature without finding the cited input. Stdin probes verified the tail-length and binary-cardinality mismatches. Proposed this unchanged Brändén–Huh consequence as prior input; no new helper, assumption or import was introduced.
* 2026-10-09 · open · stated the exact original-variable mixed-directional prerequisite and proved its empty-direction branch using BinaryRankWeightSignature; direct list induction cannot use its quadratic induction hypothesis on the cubic tail.
-/
