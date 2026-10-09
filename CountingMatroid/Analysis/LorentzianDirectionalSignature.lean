import CountingMatroid.Analysis.QuadraticSignatureHyperplane
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false

/-!
Coordinate certificates for the Lorentzian argument. The certificate records
homogeneous degree, nonnegative coefficients, M-convex support, and the
positive-signature bound for every quadratic coordinate derivative. The
general passage from coordinate derivatives to nonnegative directional
derivatives remains open; its degree-two case is proved below. The missing
passage is the borrowed Brändén–Huh closure consequence cited at
main.tex:340-348. A statement-shape search of the pinned Mathlib and Arlib
sources found no applicable Lorentzian, M-convex polynomial, or
nonnegative directional-signature closure declaration.
-/

namespace CountingMatroid.Analysis.LorentzianDirectionalSignature

open scoped BigOperators

/-- INTERNAL: The exchange condition for the exponent support of a homogeneous
polynomial. Subtraction is coordinatewise natural subtraction; the strict
inequality at `i` ensures that the removed unit is present.
TEXLINE: main.tex:334-348 -/
def HasMConvexSupport {σ : Type} (p : MvPolynomial σ ℚ) : Prop :=
  ∀ x ∈ p.support, ∀ y ∈ p.support, ∀ i, y i < x i →
    ∃ j, x j < y j ∧
      x - Finsupp.single i 1 + Finsupp.single j 1 ∈ p.support

/-- INTERNAL: The real quadratic form attached to the rational constant
Hessian, including the zero polynomial.
TEXLINE: main.tex:326-348 -/
noncomputable def constantHessianForm {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) : QuadraticForm ℝ (σ → ℝ) := by
  classical
  exact Matrix.toQuadraticForm' (fun i j =>
    ((MvPolynomial.constantCoeff (MvPolynomial.pderiv i (MvPolynomial.pderiv j p)) : ℚ) : ℝ))

/-- INTERNAL: A coordinate certificate separates the matroid-specific base
result from the general Lorentzian directional-closure result. In particular,
its last field quantifies only over coordinate derivatives, not directions.
TEXLINE: main.tex:334-348 -/
structure CoordinateLorentzian {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) : Prop where
  homogeneous : p.IsHomogeneous n
  coeff_nonneg : ∀ m, 0 ≤ p.coeff m
  exchange : HasMConvexSupport p
  coordinate_signature : ∀ xs : List σ, xs.length + 2 = n →
    sigPos (constantHessianForm
      (xs.foldr (fun s f => MvPolynomial.pderiv s f) p)) ≤ 1

/-- INTERNAL: At degree two the coordinate certificate already contains the
required Hessian bound; there are no directional derivatives left to take.
TEXLINE: main.tex:340-348 -/
theorem degree_two_directional_signature {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (hp : CoordinateLorentzian p 2)
    (ds : List (σ → ℚ)) (hlength : ds.length + 2 = 2) :
    sigPos (constantHessianForm
      (ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p)) ≤ 1 := by
  have hnil : ds = [] := by
    apply List.eq_nil_iff_length_eq_zero.mpr
    omega
  subst ds
  exact hp.coordinate_signature [] rfl

/-- PAPER: main.tex:340-348
The nonnegative directional-closure consequence of the Lorentzian coordinate
certificate, specialized to rational coefficients and a quadratic result.
BORROWED: Brändén–Huh, Lorentzian polynomials (2020), Theorems 2.10 and
Corollary 2.11, with the defining quadratic signature property. -/
theorem directional_hessian_sigPos_le_one {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n)
    (ds : List (σ → ℚ)) (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s)
    (hlength : ds.length + 2 = n) :
    sigPos (constantHessianForm
      (ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p)) ≤ 1 := by
  by_cases hn : n = 2
  · rw [hn] at hp hlength
    exact degree_two_directional_signature p hp ds hlength
  · -- BLOCKER: the coordinate-signature field gives separate nonpositive
    -- hyperplanes. A sum of such forms need not share a hyperplane. The
    -- M-convex support and compatibility inherited from one homogeneous
    -- polynomial are needed for the general Lorentzian closure argument.
    -- Direct list induction cannot use hp.coordinate_signature as an
    -- invariant for the tail: before the last derivative the degree is 3.
    -- BLOCKER (library name not found): searched pinned Mathlib and Arlib
    -- for Lorentzian/M-convex/log-concave polynomial theory, nonnegative
    -- substitution and directional closure, and polynomial Hessian sigPos
    -- bounds. No applicable declaration was found. The needed closure is:
    -- CoordinateLorentzian f (k + 1) -> (forall s, 0 <= d s) ->
    -- CoordinateLorentzian (sum s, C (d s) * pderiv s f) k.
    -- Applying degree_two_directional_signature p to the general goal
    -- leaves CoordinateLorentzian p 2 and ds.length + 2 = 2, not consequences
    -- of hp and hlength. Applying HasNonpositiveHyperplane.sigPos_le_one
    -- instead leaves a common nonpositive hyperplane for the mixed Hessian;
    -- the coordinate certificates do not directly supply that witness.
    -- PRIOR-PROPOSAL: this unchanged declaration is the precise quadratic
    -- consequence needed here of BH2020 Theorem 2.10 and Corollary 2.11,
    -- explicitly invoked without proof at main.tex:340-348.
    sorry

end CountingMatroid.Analysis.LorentzianDirectionalSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · blocked · preserved the degree-two proof; statement-shape searches of pinned Mathlib and Arlib found no Lorentzian directional closure result. Stdin applications of the degree-two and hyperplane bounds exposed, respectively, a degree-two certificate/length mismatch and a missing common nonpositive hyperplane. Proposed the unchanged borrowed directional signature declaration as prior input; added no helper, assumption, or import.
-/
