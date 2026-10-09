import CountingMatroid.Analysis.QuadraticSignatureHyperplane
import CountingMatroid.Analysis.NonnegativeDirectionalMConvexSupport
import CountingMatroid.Analysis.CubicDirectionalSignature
import Mathlib.RingTheory.MvPolynomial.EulerIdentity
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.MvPolynomial.Homogeneous

set_option autoImplicit false

/-!
Coordinate certificates for the Lorentzian argument record homogeneous degree,
nonnegative coefficients, M-convex support, and the positive-signature bound
for every quadratic coordinate derivative. The directional signature theorem
is reduced to two independent obligations: M-convex support preservation under
nonnegative directional differentiation, and the cubic signature mixing step.
The coefficient/support calculations and the reduction through coordinate and
directional derivative lists are implemented. The two imported obligations
remain open, so the general theorem is not yet a completed proof. The original
degree-two proof is preserved.

The paper invokes the Brändén–Huh closure results at main.tex:340-348. The pinned
libraries contain homogeneous partial-derivative and quadratic-signature APIs,
but no applicable Lorentzian or M-convex directional-closure theorem was found.

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

/-- INTERNAL: Coordinate differentiation preserves the coordinate certificate;
the exchange field uses the separately isolated support-deletion lemma.
TEXLINE: main.tex:340-348 -/
theorem coordinate_pderiv_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n) (s : σ) :
    CoordinateLorentzian (MvPolynomial.pderiv s p) (n - 1) := by
  classical
  refine ⟨hp.homogeneous.pderiv, ?_, ?_, ?_⟩
  · intro m
    rw [MvPolynomial.coeff_pderiv]
    exact mul_nonneg (hp.coeff_nonneg _) (by positivity)
  · have hd : ∀ t : σ, 0 ≤ (Pi.single s (1 : ℚ) : σ → ℚ) t := by
      intro t
      simp only [Pi.single_apply]
      split_ifs <;> norm_num
    have h := NonnegativeDirectionalMConvexSupport.nonnegative_directional_mconvex_support
      p n hp.homogeneous hp.coeff_nonneg hp.exchange (Pi.single s 1) hd
    simpa [HasMConvexSupport, Pi.single_apply] using h
  · intro xs hxs
    have hlen : (xs ++ [s]).length + 2 = n := by
      simp only [List.length_append, List.length_singleton]
      omega
    simpa only [List.foldr_append, List.foldr_cons, List.foldr_nil] using
      hp.coordinate_signature (xs ++ [s]) hlen

/-- INTERNAL: The coordinate certificate descends through a list of partial
derivatives, with the degree decreased by the list's length.
TEXLINE: main.tex:340-348 -/
theorem coordinate_fold_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (n : ℕ) (hp : CoordinateLorentzian p n) (xs : List σ) :
    CoordinateLorentzian (xs.foldr (fun s f => MvPolynomial.pderiv s f) p)
      (n - xs.length) := by
  induction xs generalizing n with
  | nil => simpa using hp
  | cons s xs ih =>
    have h := coordinate_pderiv_certificate _ (n - xs.length) (ih n hp) s
    simpa only [List.foldr_cons, List.length_cons, Nat.sub_sub] using h

/-- INTERNAL: Rational polynomial partial derivatives commute coefficientwise.
TEXLINE: main.tex:340-348 -/
theorem coordinate_pderiv_commute {σ : Type} (p : MvPolynomial σ ℚ) (i j : σ) :
    MvPolynomial.pderiv i (MvPolynomial.pderiv j p) =
      MvPolynomial.pderiv j (MvPolynomial.pderiv i p) := by
  classical
  ext m
  simp only [MvPolynomial.coeff_pderiv]
  by_cases hij : i = j
  · subst j
    rfl
  · simp [Finsupp.add_apply, hij, Ne.symm hij,
      add_comm, add_left_comm, mul_assoc, mul_comm, mul_left_comm]

/-- INTERNAL: A coordinate derivative list commutes with a rational directional
derivative, allowing the signature field to be checked on cubic derivatives.
TEXLINE: main.tex:340-348 -/
theorem coordinate_fold_directional_commute {σ : Type} [Fintype σ]
    (xs : List σ) (p : MvPolynomial σ ℚ) (d : σ → ℚ) :
    xs.foldr (fun s f => MvPolynomial.pderiv s f)
      (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p) =
    ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s
      (xs.foldr (fun s f => MvPolynomial.pderiv s f) p) := by
  classical
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.foldr_cons, ih, map_sum, MvPolynomial.pderiv_C_mul]
    simp only [coordinate_pderiv_commute _ i]

/-- INTERNAL: Support preservation and cubic mixing together preserve the
coordinate certificate under one nonnegative directional derivative.
TEXLINE: main.tex:340-348 -/
theorem directional_derivative_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (k : ℕ) (hp : CoordinateLorentzian p (k + 3))
    (d : σ → ℚ) (hd : ∀ s, 0 ≤ d s) :
    CoordinateLorentzian
      (∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s p) (k + 2) := by
  classical
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply MvPolynomial.IsHomogeneous.sum
    intro s _
    simpa using hp.homogeneous.pderiv.C_mul (d s)
  · exact NonnegativeDirectionalMConvexSupport.directional_coeff_nonnegative p
      hp.coeff_nonneg d hd
  · exact NonnegativeDirectionalMConvexSupport.nonnegative_directional_mconvex_support
      p (k + 3) hp.homogeneous hp.coeff_nonneg hp.exchange d hd
  · intro xs hxs
    have hdegree : k + 3 - xs.length = 3 := by omega
    have hcert := coordinate_fold_certificate p (k + 3) hp xs
    rw [hdegree] at hcert
    rw [coordinate_fold_directional_commute]
    exact CubicDirectionalSignature.cubic_directional_signature _ hcert.homogeneous
      hcert.coeff_nonneg hcert.exchange
      (fun s => hcert.coordinate_signature [s] rfl) d hd

/-- INTERNAL: Iterating one-step directional closure leaves the degree
specified by the remaining coordinate certificate.
TEXLINE: main.tex:340-348 -/
theorem directional_fold_certificate {σ : Type} [Fintype σ]
    (p : MvPolynomial σ ℚ) (ds : List (σ → ℚ)) (k : ℕ)
    (hp : CoordinateLorentzian p (ds.length + k + 2))
    (hds : ∀ d ∈ ds, ∀ s, 0 ≤ d s) :
    CoordinateLorentzian
      (ds.foldr (fun d f => ∑ s, MvPolynomial.C (d s) * MvPolynomial.pderiv s f) p)
      (k + 2) := by
  induction ds generalizing k with
  | nil => simpa using hp
  | cons d ds ih =>
    have hp' : CoordinateLorentzian p (ds.length + (k + 1) + 2) := by
      simpa only [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hp
    have htail := ih (k + 1) hp' (fun e he => hds e (List.mem_cons_of_mem d he))
    exact directional_derivative_certificate _ k
      (by simpa only [Nat.add_assoc] using htail)
      d (hds d (List.mem_cons_self))

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
  · have hp' : CoordinateLorentzian p (ds.length + 0 + 2) := by
      simpa only [Nat.add_zero, hlength] using hp
    exact (directional_fold_certificate p ds 0 hp' hds).coordinate_signature [] rfl

end CountingMatroid.Analysis.LorentzianDirectionalSignature

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · validated parallel handoff · request agent1-directional-cubic-support-20261009-1 accepted at semantic-use stage; NonnegativeDirectionalMConvexSupport and CubicDirectionalSignature transferred to scheduler ownership. The unchanged target has a complete proof body using both children; its remaining mathematical proof debt is explicitly retained in those two open obligations.
* 2026-10-09 · decomposed · directional signature reduced to independently stated support-exchange preservation and cubic signature mixing; proved coefficient positivity, exact directional support membership, coordinate commutation, and the parent reduction. The two child obligations remain open pending live handoff.
* 2026-10-09 · blocked · preserved the degree-two proof; statement-shape searches of pinned Mathlib and Arlib found no Lorentzian directional closure result. Stdin applications of the degree-two and hyperplane bounds exposed, respectively, a degree-two certificate/length mismatch and a missing common nonpositive hyperplane. Proposed the unchanged borrowed directional signature declaration as prior input; added no helper, assumption, or import.
-/
