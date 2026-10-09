import CountingMatroid.Analysis.DefectPartitionQuadraticConstruction

set_option autoImplicit false

/-!
The derivative and substitution construction of the omitted-label quadratic
at a slot recursion node. Its descendant and degree properties concern a
matroid rank polynomial; they do not identify operational oracle weights.
-/

namespace CountingMatroid.Analysis.OmittedSlotQuadratic

open CountingMatroid.Model
open CountingMatroid.Analysis.RankWeightQuadraticSignature
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction
open scoped BigOperators

/-- INTERNAL: Labels forced to be omitted at a slot node.
TEXLINE: main.tex:584-593 -/
noncomputable def fixedOmissions {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n)) :
    PairedSet n := Finset.univ \ (B ∪ R ∪ U.product Finset.univ)

/-- INTERNAL: Delete the homogenizing variable, retaining omitted labels.
TEXLINE: main.tex:354-367 -/
noncomputable def omitHomogenizer {n : ℕ} :
    Option (PairedGround n) → PairedGround n → ℚ
  | none, _ => 0
  | some e, f => if e = f then 1 else 0

/-- INTERNAL: Differentiate in each fixed omitted label.
TEXLINE: main.tex:584-586 -/
noncomputable def differentiateLabels {n : ℕ} (C : PairedSet n)
    (g : MvPolynomial (PairedGround n) ℚ) : MvPolynomial (PairedGround n) ℚ :=
  C.toList.foldl (fun p e => MvPolynomial.pderiv e p) g

/-- INTERNAL: Delete fixed labels, and identify the two labels of each
ordinary slot except the next one, using its false label as representative.
TEXLINE: main.tex:586-589 -/
noncomputable def slotSubstitution {n : ℕ} (R : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) : PairedGround n → PairedGround n → ℚ :=
  fun e f => if e ∈ R ∨ e.1 = t then (if e = f then 1 else 0)
    else if e.1 ∈ U.erase t then (if (e.1, false) = f then 1 else 0) else 0

/-- INTERNAL: Extract exponent exactly one in an ordinary-slot variable.
TEXLINE: main.tex:369-373,587-589 -/
noncomputable def extractLabel {n : ℕ} (e : PairedGround n)
    (g : MvPolynomial (PairedGround n) ℚ) : MvPolynomial (PairedGround n) ℚ :=
  linearSubstitution (fun s f => if s = e then 0 else if s = f then 1 else 0)
    (MvPolynomial.pderiv e g)

/-- INTERNAL: Relabel the surviving variables by the old-hole subtype and
the two new labels.
TEXLINE: main.tex:592-601 -/
noncomputable def activeSubstitution {n : ℕ} (R : PairedSet n) (t : Fin n) :
    PairedGround n → (R ⊕ Bool) → ℚ
  | e, .inl i => if e = i then 1 else 0
  | e, .inr b => if e = (t, b) then 1 else 0

/-- INTERNAL: The actual omitted-label slot extraction, starting with the
homogenized Tutte polynomial of the dual paired matroid. The normalization
is the paper's q^n/n!.
TEXLINE: main.tex:354-367,584-601 -/
noncomputable def omittedSlotQuadratic {n : ℕ} (N : Matroid (PairedGround n))
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n) :
    MvPolynomial (R ⊕ Bool) ℚ := by
  classical
  let F := linearSubstitution omitHomogenizer
    ((MvPolynomial.pderiv none)^[n] (tuttePolynomial N q))
  let G := linearSubstitution (slotSubstitution R U t)
    (differentiateLabels (fixedOmissions B R U) F)
  let H := (U.erase t).toList.foldl (fun p s => extractLabel (s, false) p) G
  exact MvPolynomial.C (q ^ n / (n.factorial : ℚ)) *
    linearSubstitution (activeSubstitution R t) H

/-- INTERNAL: The extraction is composed only of the closure operations
allowed in the cited signature theorem.
TEXLINE: main.tex:326-373,584-601 -/
theorem omitted_slot_descendant {n : ℕ} (N : Matroid (PairedGround n))
    (q : ℚ) (hq : 0 < q) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n) :
    Descendant (tuttePolynomial N q) (R ⊕ Bool)
      (omittedSlotQuadratic N q B R U t) := by
  classical
  let T := tuttePolynomial N q
  have hiter (m : ℕ) : Descendant T (Option (PairedGround n))
      ((MvPolynomial.pderiv none)^[m] T) := by
    induction m with
    | zero => exact Descendant.initial
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact Descendant.derivative none ih
  have hF : Descendant T (PairedGround n)
      (linearSubstitution omitHomogenizer ((MvPolynomial.pderiv none)^[n] T)) := by
    apply Descendant.substitute _ _ (hiter n)
    intro e f
    cases e <;> simp [omitHomogenizer]
    split_ifs <;> norm_num
  have hdiff (l : List (PairedGround n)) (g : MvPolynomial (PairedGround n) ℚ)
      (hg : Descendant T (PairedGround n) g) :
      Descendant T (PairedGround n) (l.foldl (fun p e => MvPolynomial.pderiv e p) g) := by
    induction l generalizing g with
    | nil => exact hg
    | cons e l ih => exact ih _ (Descendant.derivative e hg)
  have hG := Descendant.substitute (slotSubstitution R U t)
    (by intro e f; unfold slotSubstitution; split_ifs <;> norm_num)
    (hdiff (fixedOmissions B R U).toList _ hF)
  have hextract (l : List (Fin n)) (g : MvPolynomial (PairedGround n) ℚ)
      (hg : Descendant T (PairedGround n) g) :
      Descendant T (PairedGround n)
        (l.foldl (fun p s => extractLabel (s, false) p) g) := by
    induction l generalizing g with
    | nil => exact hg
    | cons s l ih =>
      apply ih
      apply Descendant.substitute _ _ (Descendant.derivative (s, false) hg)
      intro e f
      split_ifs <;> norm_num
  apply Descendant.scale _ (by positivity)
  apply Descendant.substitute _ _ (hextract (U.erase t).toList _ hG)
  intro e f
  cases f <;> simp only [activeSubstitution] <;> split_ifs <;> norm_num

/-- INTERNAL: The node's disjointness and size invariant count exactly the
fixed omitted labels used by the extraction.
TEXLINE: main.tex:589-591 -/
theorem fixed_omissions_card {n : ℕ} (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1) :
    (fixedOmissions B R U).card + U.card = n - 1 := by
  classical
  have hd : Disjoint (B ∪ R) (U.product Finset.univ) := by
    rw [Finset.disjoint_left]
    rintro ⟨s, b⟩ he hf
    have hs := (Finset.mem_product.mp hf).1
    rcases Finset.mem_union.mp he with he | he
    · exact (hU s hs b).1 he
    · exact (hU s hs b).2 he
  have hc : (B ∪ R ∪ U.product Finset.univ).card = B.card + R.card + 2 * U.card := by
    rw [Finset.card_union_of_disjoint hd, Finset.card_union_of_disjoint hBR]
    change B.card + R.card + (U ×ˢ (Finset.univ : Finset Bool)).card = _
    rw [Finset.card_product]
    simp [Nat.mul_comm]
  have hle := Finset.card_le_univ (B ∪ R ∪ U.product Finset.univ)
  have htotal : Fintype.card (PairedGround n) = 2 * n := by
    simp [PairedGround, Nat.mul_comm]
  rw [hc, htotal] at hle
  unfold fixedOmissions
  rw [Finset.card_sdiff_of_subset (Finset.subset_univ _), Finset.card_univ, htotal, hc]
  omega

/-- INTERNAL: The extraction leaves exactly degree two, including nodes
with no ordinary slot after the next slot.
TEXLINE: main.tex:589-591 -/
theorem omitted_slot_homogeneous {n : ℕ} (N : Matroid (PairedGround n))
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n))
    (hBR : Disjoint B R)
    (hU : ∀ t ∈ U, ∀ b : Bool, (t, b) ∉ B ∧ (t, b) ∉ R)
    (hsize : B.card + R.card + U.card = n + 1)
    (t : Fin n) (ht : t ∈ U) :
    (omittedSlotQuadratic N q B R U t).IsHomogeneous 2 := by
  classical
  let T := tuttePolynomial N q
  have hT : T.IsHomogeneous (2 * n) := by
    simpa [T, PairedGround, Nat.mul_comm] using tutte_polynomial_homogeneous N q
  have hiter (m : ℕ) : ((MvPolynomial.pderiv none)^[m] T).IsHomogeneous (2 * n - m) := by
    induction m with
    | zero => simpa using hT
    | succ m ih =>
      rw [Function.iterate_succ_apply']
      simpa [Nat.sub_sub] using ih.pderiv (i := none)
  have hF : (linearSubstitution omitHomogenizer
      ((MvPolynomial.pderiv none)^[n] T)).IsHomogeneous n := by
    simpa only [show 2 * n - n = n by omega] using
      linear_substitution_homogeneous omitHomogenizer _ _ (hiter n)
  have hdiff (l : List (PairedGround n)) (g : MvPolynomial (PairedGround n) ℚ)
      (d : ℕ) (hg : g.IsHomogeneous d) :
      (l.foldl (fun p e => MvPolynomial.pderiv e p) g).IsHomogeneous (d - l.length) := by
    induction l generalizing g d with
    | nil => simpa using hg
    | cons e l ih => simpa [Nat.sub_sub, Nat.add_comm] using ih _ (d - 1) hg.pderiv
  have hG := linear_substitution_homogeneous (slotSubstitution R U t) _ _
    (hdiff (fixedOmissions B R U).toList _ n hF)
  have hextract (l : List (Fin n)) (g : MvPolynomial (PairedGround n) ℚ)
      (d : ℕ) (hg : g.IsHomogeneous d) :
      (l.foldl (fun p s => extractLabel (s, false) p) g).IsHomogeneous (d - l.length) := by
    induction l generalizing g d with
    | nil => simpa using hg
    | cons s l ih =>
      have hs := linear_substitution_homogeneous
        (fun e f : PairedGround n => if e = (s, false) then 0 else if e = f then 1 else 0)
        _ _ (hg.pderiv (i := (s, false)))
      simpa [extractLabel, Nat.sub_sub, Nat.add_comm] using ih _ (d - 1) hs
  have hH := hextract (U.erase t).toList _ _ hG
  have hcard := fixed_omissions_card B R U hBR hU hsize
  have hpos : 0 < U.card := Finset.card_pos.mpr ⟨t, ht⟩
  have hdeg : n - (fixedOmissions B R U).toList.length - (U.erase t).toList.length = 2 := by
    rw [Finset.length_toList, Finset.length_toList, Finset.card_erase_of_mem ht]
    have hn := t.isLt
    omega
  rw [hdeg] at hH
  exact (linear_substitution_homogeneous (activeSubstitution R t) _ _ hH).C_mul _

end CountingMatroid.Analysis.OmittedSlotQuadratic
