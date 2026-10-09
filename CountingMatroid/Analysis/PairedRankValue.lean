import CountingMatroid.Analysis.GreedyRankCorrect
import CountingMatroid.Analysis.DefectPartitionQuadraticConstruction

set_option autoImplicit false

/-!
The value of the paired-rank program on an arbitrary paired set, expressed
through the two original matroid ranks. This evaluates the charged projection
scan as well as its two greedy scans, without introducing a rank oracle.
-/

namespace CountingMatroid.Analysis.PairedRankValue

open CountingMatroid.Model
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.DefectPartitionQuadraticExtraction

/-- INTERNAL: The paired projection scan on an arbitrary set computes its
x indices, the complement of its y indices, and its y cardinality.
TEXLINE: main.tex:270-280,1333-1346 -/
theorem paired_projections_value {n : ℕ} (state : PairedSet n) :
    (pairedProjections state).val =
      (Finset.univ.filter (fun i => (i, false) ∈ state),
       Finset.univ.filter (fun i => (i, true) ∉ state),
       (Finset.univ.filter (fun i => (i, true) ∈ state)).card) := by
  classical
  let step : (Finset (Fin n) × Finset (Fin n) × ℕ) → Fin n →
      Arlib.Computation.Charged Operations.Op Operations.Cell
        (Finset (Fin n) × Finset (Fin n) × ℕ) := fun acc i => do
    let inX ← Operations.containsPaired state (i, false)
    let x ← if inX then Operations.insertElement acc.1 i else pure acc.1
    let inY ← Operations.containsPaired state (i, true)
    if inY then
      let ysize ← Operations.successor acc.2.2
      pure (x, acc.2.1, ysize)
    else
      let complementY ← Operations.insertElement acc.2.1 i
      pure (x, complementY, acc.2.2)
  have hstep (x y : Finset (Fin n)) (k : ℕ) (i : Fin n) :
      (step (x, y, k) i).val =
        (if (i, false) ∈ state then insert i x else x,
         if (i, true) ∈ state then y else insert i y,
         if (i, true) ∈ state then k + 1 else k) := by
    by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
      simp [step, Operations.containsPaired, Operations.insertElement,
        Operations.successor, hx, hy]
  have hfold (l : List (Fin n)) (x y : Finset (Fin n)) (k : ℕ) :
      (Arlib.Computation.Charged.foldl step l (x, y, k)).val =
        (x ∪ (l.filter (fun i => (i, false) ∈ state)).toFinset,
         y ∪ (l.filter (fun i => (i, true) ∉ state)).toFinset,
         k + (l.filter (fun i => (i, true) ∈ state)).length) := by
    induction l generalizing x y k with
    | nil => simp
    | cons i l ih =>
      rw [Arlib.Computation.Charged.val_foldl_cons, hstep]
      by_cases hx : (i, false) ∈ state <;> by_cases hy : (i, true) ∈ state <;>
        simp [hx, hy, ih, Finset.union_insert, Finset.insert_union,
          Nat.add_assoc, Nat.add_comm]
  change (Arlib.Computation.Charged.foldl step (List.finRange n)
    ((∅ : Finset (Fin n)), (∅ : Finset (Fin n)), 0)).val = _
  rw [hfold]
  have hf (p : Fin n → Prop) [DecidablePred p] :
      ((List.finRange n).filter p).toFinset = Finset.univ.filter p := by
    ext i
    simp
  have hlen : ((List.finRange n).filter (fun i => (i, true) ∈ state)).length =
      (Finset.univ.filter (fun i => (i, true) ∈ state)).card := by
    rw [← List.toFinset_card_of_nodup ((List.nodup_finRange n).filter _), hf]
  simp only [Finset.empty_union, zero_add, hf, hlen]

/-- INTERNAL: Arbitrary paired-rank calls are evaluated by the original
independence oracles as the paper's two-rank formula. The `.toNat` terms
are finite matroid ranks, and the program's final subtraction is retained.
TEXLINE: main.tex:270-280,1333-1346 -/
theorem paired_rank_value {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (h₁ : ExactOracle M₁ o₁) (h₂ : ExactOracle M₂ o₂) (state : PairedSet n) :
    (pairedRank r o₁ o₂ state).val =
      (M₁.eRk {i | (i, false) ∈ state}).toNat +
        (Finset.univ.filter (fun i => (i, true) ∈ state)).card +
        (M₂.eRk {i | (i, true) ∉ state}).toNat - r := by
  classical
  have hX := GreedyRankCorrect.greedyRank_eq_eRk M₁ o₁ hfull.1 h₁ false
    (Finset.univ.filter (fun i => (i, false) ∈ state))
  have hY := GreedyRankCorrect.greedyRank_eq_eRk M₂ o₂ hfull.2 h₂ true
    (Finset.univ.filter (fun i => (i, true) ∉ state))
  have hX' : (greedyRank false o₁ (Finset.univ.filter (fun i => (i, false) ∈ state))).val =
      (M₁.eRk {i | (i, false) ∈ state}).toNat := by
    simpa using congrArg ENat.toNat hX
  have hY' : (greedyRank true o₂ (Finset.univ.filter (fun i => (i, true) ∉ state))).val =
      (M₂.eRk {i | (i, true) ∉ state}).toNat := by
    simpa using congrArg ENat.toNat hY
  unfold pairedRank
  simp only [Arlib.Computation.Charged.val_bind, paired_projections_value,
    Operations.natAdd, Operations.natSub, Arlib.Computation.Charged.val_op]
  rw [hX', hY']

/-- INTERNAL: The rank of the paired direct sum is the sum of the ranks
of its two label fibers. This follows from bases of the two fibers.
TEXLINE: main.tex:262-272 -/
theorem paired_matroid_eRk {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (hfull : FullGround M₁ M₂) (S : Set (PairedGround n)) :
    (pairedMatroid M₁ M₂).eRk S =
      M₁.eRk {i | (i, false) ∈ S} + M₂✶.eRk {i | (i, true) ∈ S} := by
  classical
  obtain ⟨I, hI⟩ := M₁.exists_isBasis {i | (i, false) ∈ S}
    (by rw [hfull.1]; exact Set.subset_univ _)
  obtain ⟨J, hJ⟩ := M₂✶.exists_isBasis {i | (i, true) ∈ S}
    (by rw [Matroid.dual_ground, hfull.2]; exact Set.subset_univ _)
  let K : Set (PairedGround n) :=
    (fun i => (i, false)) '' I ∪ (fun i => (i, true)) '' J
  have hK : (pairedMatroid M₁ M₂).IsBasis K S := by
    rw [pairedMatroid, Matroid.mapEquiv_isBasis_iff, Matroid.sum'_isBasis_iff]
    intro b
    cases b
    · simpa [K, Set.preimage, Set.image_union, Set.ext_iff] using hI
    · simpa [K, Set.preimage, Set.image_union, Set.ext_iff] using hJ
  have hd : Disjoint ((fun i : Fin n => (i, false)) '' I)
      ((fun i : Fin n => (i, true)) '' J) := by
    rw [Set.disjoint_left]
    rintro e ⟨i, hi, rfl⟩ ⟨j, hj, he⟩
    simp at he
  have hinj (b : Bool) : Function.Injective (fun i : Fin n => (i, b)) :=
    fun _ _ h => congrArg Prod.fst h
  rw [hK.eRk_eq_encard]
  dsimp only [K]
  rw [Set.encard_union_eq hd, (hinj false).encard_image,
    (hinj true).encard_image, hI.encard_eq_eRk, hJ.encard_eq_eRk]

/-- PAPER: main.tex:270-280
The paired-rank program computes the rank of the paired matroid on every
paired set, using only the two supplied original independence oracles. -/
theorem paired_rank_eq_eRk {n : ℕ} (r : ℕ) (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (hfull : FullGround M₁ M₂)
    (hr : CommonRank r M₁ M₂) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (state : PairedSet n) :
    (pairedRank r o₁ o₂ state).val =
      ((pairedMatroid M₁ M₂).eRk (state : Set (PairedGround n))).toNat := by
  classical
  let Y : Set (Fin n) := {i | (i, true) ∈ state}
  let Z : Set (Fin n) := {i | (i, true) ∉ state}
  have hfinite (M : Matroid (Fin n)) (S : Set (Fin n)) : M.eRk S ≠ ⊤ :=
    (M.isRkFinite_of_finite (Set.toFinite S)).eRk_lt_top.ne
  have hcard : Y.encard =
      ((Finset.univ.filter (fun i => (i, true) ∈ state)).card : ℕ∞) := by
    have hs : Y = (Finset.univ.filter (fun i => (i, true) ∈ state) : Set (Fin n)) := by
      ext i
      simp [Y]
    rw [hs]
    exact Set.encard_coe_eq_coe_finsetCard _
  have hcompl : M₂.E \ Y = Z := by
    rw [hfull.2]
    ext i
    simp [Y, Z]
  have hd := M₂.eRk_dual_add_eRank Y (by rw [hfull.2]; exact Set.subset_univ _)
  rw [hr.2, hcompl, hcard] at hd
  have hd' : (M₂✶.eRk Y).toNat + r =
      (M₂.eRk Z).toNat + (Finset.univ.filter (fun i => (i, true) ∈ state)).card := by
    have hh := congrArg ENat.toNat hd
    simpa only [ENat.toNat_add (hfinite M₂✶ Y) (ENat.coe_ne_top r),
      ENat.toNat_add (hfinite M₂ Z) (ENat.coe_ne_top _), ENat.toNat_natCast] using hh
  rw [paired_rank_value r M₁ M₂ o₁ o₂ hfull h₁ h₂,
    paired_matroid_eRk M₁ M₂ hfull,
    ENat.toNat_add (hfinite M₁ _) (hfinite M₂✶ _)]
  change (M₁.eRk _).toNat + _ + (M₂.eRk Z).toNat - r =
    (M₁.eRk _).toNat + (M₂✶.eRk Y).toNat
  simp only [Finset.mem_coe]
  omega

end CountingMatroid.Analysis.PairedRankValue
