import CountingMatroid.Analysis.DefectSlotSplitSignature

set_option autoImplicit false

/-!
Binary completion identities used by the balanced-hole recursion. Processing
one ordinary pair partitions each old-hole completion into its two children.
The corresponding future-slot matrix identities give conservation of the
future quadratic forms; these identities use finite sets, not a signature
assumption.
-/

namespace CountingMatroid.Analysis.DefectSlotConservation

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.DefectSlotSplitSignature
open scoped BigOperators

/-- INTERNAL: Separate the chosen label of the pair being processed from
its remaining completion labels.
TEXLINE: main.tex:531-540 -/
private theorem choice_image_split {n : ℕ} (U : Finset (Fin n))
    (t : Fin n) (ht : t ∈ U) (choices : Fin n → Bool) :
    U.image (fun s => (s, choices s)) =
      insert (t, choices t) ((U.erase t).image (fun s => (s, choices s))) := by
  classical
  conv_lhs => rw [← Finset.insert_erase ht, Finset.image_insert]

/-- INTERNAL: A free binary pair can be selected in exactly its two
possible ways; choices at all other pairs stay unchanged.
TEXLINE: main.tex:531-540 -/
private theorem choice_completion_split {n : ℕ} (Q : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (ht : t ∈ U) (state : PairedSet n) :
    (∃ choices : Fin n → Bool,
      state = Q ∪ U.image (fun s => (s, choices s))) ↔
    (∃ choices : Fin n → Bool,
      state = insert (t, false) Q ∪ (U.erase t).image (fun s => (s, choices s))) ∨
    (∃ choices : Fin n → Bool,
      state = insert (t, true) Q ∪ (U.erase t).image (fun s => (s, choices s))) := by
  classical
  constructor
  · rintro ⟨choices, rfl⟩
    rw [choice_image_split U t ht choices]
    cases choices t
    · left
      exact ⟨choices, by simp⟩
    · right
      exact ⟨choices, by simp⟩
  · have lift (c : Bool) (choices : Fin n → Bool)
        (hs : state = insert (t, c) Q ∪
          (U.erase t).image (fun s => (s, choices s))) :
        ∃ choices : Fin n → Bool,
          state = Q ∪ U.image (fun s => (s, choices s)) := by
      refine ⟨Function.update choices t c, ?_⟩
      have himage : (U.erase t).image (fun s => (s, Function.update choices t c s)) =
          (U.erase t).image (fun s => (s, choices s)) := by
        apply Finset.image_congr
        intro s hs
        dsimp only
        rw [Function.update_of_ne (Finset.ne_of_mem_erase hs)]
      rw [choice_image_split U t ht, Function.update_self, himage]
      simpa using hs
    rintro (⟨choices, hs⟩ | ⟨choices, hs⟩)
    · exact lift false choices hs
    · exact lift true choices hs

/-- INTERNAL: After a pair has been processed, precisely its chosen label
occurs, provided neither of its labels is fixed in the base.
TEXLINE: main.tex:531-540 -/
private theorem child_membership {n : ℕ} (Q : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (hQ : ∀ c : Bool, (t, c) ∉ Q)
    (c d : Bool) (state : PairedSet n)
    (hs : ∃ choices : Fin n → Bool,
      state = insert (t, c) Q ∪ (U.erase t).image (fun s => (s, choices s))) :
    (t, d) ∈ state ↔ d = c := by
  classical
  obtain ⟨choices, rfl⟩ := hs
  have hn : (t, d) ∉ (U.erase t).image (fun s => (s, choices s)) := by
    rintro hm
    obtain ⟨s, hs, heq⟩ := Finset.mem_image.mp hm
    have hst : s = t := congrArg Prod.fst heq
    exact (Finset.ne_of_mem_erase hs) hst
  simp [hQ d, hn]

/-- INTERNAL: Weighted counting respects the disjoint binary completion
partition for any fixed base and any weight function.
TEXLINE: main.tex:535-540,632-639 -/
private theorem weighted_completion_split {n : ℕ} (Q : PairedSet n)
    (U : Finset (Fin n)) (t : Fin n) (ht : t ∈ U)
    (hQ : ∀ c : Bool, (t, c) ∉ Q) (f : PairedSet n → ℝ) :
    (∑ state : PairedSet n, if (∃ choices : Fin n → Bool,
      state = insert (t, false) Q ∪ (U.erase t).image (fun s => (s, choices s)))
      then f state else 0) +
    (∑ state : PairedSet n, if (∃ choices : Fin n → Bool,
      state = insert (t, true) Q ∪ (U.erase t).image (fun s => (s, choices s)))
      then f state else 0) =
    ∑ state : PairedSet n, if (∃ choices : Fin n → Bool,
      state = Q ∪ U.image (fun s => (s, choices s))) then f state else 0 := by
  classical
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state _
  let P := fun c : Bool => ∃ choices : Fin n → Bool,
    state = insert (t, c) Q ∪ (U.erase t).image (fun s => (s, choices s))
  have hexcl : P false → ¬ P true := by
    intro ha hb
    have hmem := (child_membership Q U t hQ false false state ha).mpr rfl
    have hfalse := (child_membership Q U t hQ true false state hb).mp hmem
    cases hfalse
  simp only [choice_completion_split Q U t ht state]
  change (if P false then f state else 0) + (if P true then f state else 0) =
    if P false ∨ P true then f state else 0
  by_cases ha : P false
  · rw [if_pos ha, if_neg (hexcl ha), if_pos (Or.inl ha), add_zero]
  · by_cases hb : P true
    · rw [if_neg ha, if_pos hb, if_pos (Or.inr hb), zero_add]
    · rw [if_neg ha, if_neg hb, if_neg (not_or.mpr ⟨ha, hb⟩), zero_add]

/-- PAPER: main.tex:535-540
The two child totals of any old hole add to its parent total. -/
theorem slot_total_split {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n) (ht : t ∈ U)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (hole : PairedGround n) (hhole : hole ∈ R) :
    slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) hole +
      slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) hole =
        slotTotal r o₁ o₂ q B R U hole := by
  classical
  have hne (c : Bool) : hole ≠ (t, c) := by
    rintro rfl
    exact (hfree c).2 hhole
  have hshape (c : Bool) (state : PairedSet n) :
      SlotCompletion B (insert (t, c) R) (U.erase t) hole state ↔
        ∃ choices : Fin n → Bool,
          state = insert (t, c) (B ∪ R.erase hole) ∪
            (U.erase t).image (fun s => (s, choices s)) := by
    unfold SlotCompletion
    rw [Finset.erase_insert_of_ne (hne c).symm]
    simp only [Finset.union_insert]
  have hQ (c : Bool) : (t, c) ∉ B ∪ R.erase hole := by
    simp only [Finset.mem_union, Finset.mem_erase, not_or]
    exact ⟨(hfree c).1, fun h => (hfree c).2 h.2⟩
  unfold slotTotal
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro state _
  have hsplit : SlotCompletion B R U hole state ↔
      SlotCompletion B (insert (t, false) R) (U.erase t) hole state ∨
        SlotCompletion B (insert (t, true) R) (U.erase t) hole state := by
    rw [hshape false, hshape true]
    exact choice_completion_split (B ∪ R.erase hole) U t ht state
  have hdisjoint : SlotCompletion B (insert (t, false) R) (U.erase t) hole state →
      ¬ SlotCompletion B (insert (t, true) R) (U.erase t) hole state := by
    intro ha hb
    have hmem := (child_membership _ U t hQ false false state
      ((hshape false state).mp ha)).mpr rfl
    have hfalse := (child_membership _ U t hQ true false state
      ((hshape true state).mp hb)).mp hmem
    cases hfalse
  rw [hsplit]
  by_cases ha : SlotCompletion B (insert (t, false) R) (U.erase t) hole state
  · rw [if_pos ha, if_neg (hdisjoint ha), if_pos (Or.inl ha), add_zero]
  · by_cases hb : SlotCompletion B (insert (t, true) R) (U.erase t) hole state
    · rw [if_neg ha, if_pos hb, if_pos (Or.inr hb), zero_add]
    · rw [if_neg ha, if_neg hb, if_neg (not_or.mpr ⟨ha, hb⟩), zero_add]

/-- PAPER: main.tex:540-543
The newly introduced holes count the same completions: the processed pair
is empty in either child. -/
theorem new_hole_total_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n)
    (hfree : ∀ c : Bool, (t, c) ∉ R) :
    slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false) =
      slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) (t, true) := by
  classical
  simp only [slotTotal, SlotCompletion, Finset.erase_insert (hfree _)]

/-- PAPER: main.tex:632-636
For a later pair, the entries between old holes split between the two
children, just as the old-hole totals do. -/
theorem future_matrix_split {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (B R : PairedSet n) (U : Finset (Fin n))
    (t s : Fin n) (ht : t ∈ U) (hts : t ≠ s)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (i j : PairedGround n) (hi : i ∈ R) (hj : j ∈ R) :
    futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i j +
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i j =
        futureMatrix r o₁ o₂ q B R U s i j := by
  classical
  by_cases hij : i = j
  · simp only [futureMatrix, if_pos hij, add_zero]
  have hni (c : Bool) : (t, c) ≠ i := by
    rintro rfl
    exact (hfree c).2 hi
  have hnj (c : Bool) : (t, c) ≠ j := by
    rintro rfl
    exact (hfree c).2 hj
  let Q := B ∪ (R.erase i).erase j ∪ {(s, false), (s, true)}
  have hQ (c : Bool) : (t, c) ∉ Q := by
    simp only [Q, Finset.mem_union, Finset.mem_erase, Finset.mem_insert,
      Finset.mem_singleton, Prod.mk.injEq, not_or]
    exact ⟨⟨(hfree c).1, fun h => (hfree c).2 h.2.2⟩,
      ⟨fun h => hts h.1, fun h => hts h.1⟩⟩
  have ht' : t ∈ U.erase s := Finset.mem_erase.mpr ⟨hts, ht⟩
  have hsplit := weighted_completion_split Q (U.erase s) t ht' hQ
    (fun state => ((q ^ (n -
      (CountingMatroid.Model.Subroutines.pairedRank r o₁ o₂ state).val) : ℚ) : ℝ))
  have herase : (U.erase s).erase t = (U.erase t).erase s := by
    ext x
    simp only [Finset.mem_erase]
    tauto
  simpa only [futureMatrix, if_neg hij, Finset.erase_insert_of_ne (hni _),
    Finset.erase_insert_of_ne (hnj _), Finset.union_insert, Finset.insert_union,
    herase, Finset.insert_comm, Q] using hsplit

/-- INTERNAL: The future-slot matrix is symmetric because its completion
predicate omits the same two holes in either order.
TEXLINE: main.tex:571-579 -/
theorem future_matrix_symmetric {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n)) (s : Fin n)
    (i j : PairedGround n) :
    futureMatrix r o₁ o₂ q B R U s i j =
      futureMatrix r o₁ o₂ q B R U s j i := by
  classical
  by_cases hij : i = j
  · subst j
    rfl
  have herase : (R.erase i).erase j = (R.erase j).erase i := by
    ext x
    simp only [Finset.mem_erase]
    tauto
  simp only [futureMatrix, if_neg hij, if_neg (Ne.symm hij), herase]

/-- PAPER: main.tex:636-639
A future matrix entry between an old hole and the new hole counts the same
states in either child, since the newly processed pair is then empty. -/
theorem future_matrix_new_hole_eq {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n)) (t s : Fin n)
    (hfree : ∀ c : Bool, (t, c) ∉ R)
    (i : PairedGround n) (hi : i ∈ R) :
    futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i (t, false) =
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i (t, true) := by
  classical
  have hne (c : Bool) : i ≠ (t, c) := by
    rintro rfl
    exact hfree c hi
  have hn (c : Bool) : (t, c) ∉ R.erase i := by
    exact fun h => hfree c (Finset.mem_of_mem_erase h)
  simp only [futureMatrix, if_neg (hne _),
    Finset.erase_insert_of_ne (hne _).symm, Finset.erase_insert (hn _)]

/-- INTERNAL: Expand a zero-diagonal symmetric quadratic on one newly
inserted hole into its old quadratic and the old–new cross term.
TEXLINE: main.tex:632-640 -/
private theorem child_quadratic_expansion {α : Type*} [DecidableEq α]
    (R : Finset α) (p : α) (hp : p ∉ R) (M : α → α → ℝ)
    (hsym : ∀ i j, M i j = M j i) (hdiag : M p p = 0) (h : α → ℝ) :
    (∑ i ∈ insert p R, ∑ j ∈ insert p R, M i j * h i * h j) =
      (∑ i ∈ R, ∑ j ∈ R, M i j * h i * h j) +
        2 * h p * (∑ i ∈ R, M i p * h i) := by
  classical
  simp only [Finset.sum_insert hp, hdiag, zero_mul, zero_add,
    Finset.sum_add_distrib]
  have hcross : (∑ i ∈ R, M p i * h p * h i) =
      h p * (∑ i ∈ R, M i p * h i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [hsym p i]
    ring
  have hcross' : (∑ i ∈ R, M i p * h i * h p) =
      h p * (∑ i ∈ R, M i p * h i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hcross, hcross']
  ring

/-- PAPER: main.tex:628-641
Future-slot quadratic forms are conserved by an earlier split whenever
old-hole values stay fixed and the two new-hole values are opposite. -/
theorem future_form_conserved {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n))
    (t s : Fin n) (ht : t ∈ U) (hts : t ≠ s)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (h hₐ hᵦ : PairedGround n → ℝ)
    (hkeepₐ : ∀ i ∈ R, hₐ i = h i) (hkeepᵦ : ∀ i ∈ R, hᵦ i = h i)
    (hopp : hₐ (t, false) + hᵦ (t, true) = 0) :
    (∑ i ∈ insert (t, false) R, ∑ j ∈ insert (t, false) R,
      futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i j * hₐ i * hₐ j) +
    (∑ i ∈ insert (t, true) R, ∑ j ∈ insert (t, true) R,
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i j * hᵦ i * hᵦ j) =
    ∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U s i j * h i * h j := by
  classical
  let Mₐ := futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s
  let Mᵦ := futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s
  rw [child_quadratic_expansion R (t, false) (hfree false).2 Mₐ
      (future_matrix_symmetric r o₁ o₂ q B _ _ s) (by simp [Mₐ, futureMatrix]) hₐ,
    child_quadratic_expansion R (t, true) (hfree true).2 Mᵦ
      (future_matrix_symmetric r o₁ o₂ q B _ _ s) (by simp [Mᵦ, futureMatrix]) hᵦ]
  have hold (M : PairedGround n → PairedGround n → ℝ)
      (h' : PairedGround n → ℝ) (hkeep : ∀ i ∈ R, h' i = h i) :
      (∑ i ∈ R, ∑ j ∈ R, M i j * h' i * h' j) =
        ∑ i ∈ R, ∑ j ∈ R, M i j * h i * h j := by
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    rw [hkeep i hi, hkeep j hj]
  have hcross : (∑ i ∈ R, Mᵦ i (t, true) * hᵦ i) =
      ∑ i ∈ R, Mₐ i (t, false) * hₐ i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [hkeepₐ i hi, hkeepᵦ i hi]
    dsimp only [Mₐ, Mᵦ]
    rw [future_matrix_new_hole_eq r o₁ o₂ q B R U t s
      (fun c => (hfree c).2) i hi]
  rw [hold Mₐ hₐ hkeepₐ, hold Mᵦ hᵦ hkeepᵦ, hcross]
  have hcancel : 2 * hₐ (t, false) * (∑ i ∈ R, Mₐ i (t, false) * hₐ i) +
      2 * hᵦ (t, true) * (∑ i ∈ R, Mₐ i (t, false) * hₐ i) = 0 := by
    rw [← add_mul, ← mul_add, hopp, mul_zero, zero_mul]
  calc
    _ = (∑ i ∈ R, ∑ j ∈ R, Mₐ i j * h i * h j) +
        (∑ i ∈ R, ∑ j ∈ R, Mᵦ i j * h i * h j) := by linarith [hcancel]
    _ = _ := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i hi
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j hj
      rw [← add_mul, ← add_mul]
      dsimp only [Mₐ, Mᵦ]
      rw [future_matrix_split r o₁ o₂ q B R U t s ht hts hfree i j hi hj]

/-- PAPER: main.tex:555-567
Old-hole potential is conserved, and the new holes contribute exactly the
increase stated in the paper. Their multiplier is shared by the two labels
of the processed pair. -/
theorem slot_potential_split {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ)
    (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n) (ht : t ∈ U)
    (hfree : ∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R)
    (W h hₐ hᵦ : PairedGround n → ℝ)
    (hkeepₐ : ∀ i ∈ R, hₐ i = h i) (hkeepᵦ : ∀ i ∈ R, hᵦ i = h i)
    (hW : W (t, false) = W (t, true)) :
    let sₐ := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t)
    let sᵦ := slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t)
    let u := sₐ (t, false)
    (∑ i ∈ insert (t, false) R, sₐ i * hₐ i ^ 2 / W i) +
      (∑ i ∈ insert (t, true) R, sᵦ i * hᵦ i ^ 2 / W i) =
    (∑ i ∈ R, slotTotal r o₁ o₂ q B R U i * h i ^ 2 / W i) +
      (u * hₐ (t, false) ^ 2 + u * hᵦ (t, true) ^ 2) / W (t, false) := by
  classical
  intro sₐ sᵦ u
  rw [Finset.sum_insert (hfree false).2, Finset.sum_insert (hfree true).2]
  have hold : (∑ i ∈ R, sₐ i * hₐ i ^ 2 / W i) +
      (∑ i ∈ R, sᵦ i * hᵦ i ^ 2 / W i) =
      ∑ i ∈ R, slotTotal r o₁ o₂ q B R U i * h i ^ 2 / W i := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    rw [hkeepₐ i hi, hkeepᵦ i hi, ← add_div, ← add_mul]
    rw [slot_total_split r o₁ o₂ q B R U t ht hfree i hi]
  have hu : sᵦ (t, true) = u :=
    (new_hole_total_eq r o₁ o₂ q B R U t (fun c => (hfree c).2)).symm
  rw [hu, ← hW]
  rw [add_div]
  dsimp only [u]
  linarith [hold]

/-- INTERNAL: The operational identities consumed together by the
recursive demand construction, separated from the Hessian split bound.
TEXLINE: main.tex:535-567,628-641 -/
structure SlotConservationControl (n r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) : Prop where
  old_hole : ∀ (B R : PairedSet n) (U : Finset (Fin n))
    (t : Fin n), t ∈ U →
    (∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R) →
    ∀ hole ∈ R,
      slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) hole +
        slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) hole =
          slotTotal r o₁ o₂ q B R U hole
  new_hole : ∀ (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n),
    (∀ c : Bool, (t, c) ∉ R) →
    slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t) (t, false) =
      slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t) (t, true)
  future_form : ∀ (B R : PairedSet n) (U : Finset (Fin n))
    (t s : Fin n), t ∈ U → t ≠ s →
    (∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R) →
    ∀ h hₐ hᵦ : PairedGround n → ℝ,
    (∀ i ∈ R, hₐ i = h i) → (∀ i ∈ R, hᵦ i = h i) →
    hₐ (t, false) + hᵦ (t, true) = 0 →
    (∑ i ∈ insert (t, false) R, ∑ j ∈ insert (t, false) R,
      futureMatrix r o₁ o₂ q B (insert (t, false) R) (U.erase t) s i j * hₐ i * hₐ j) +
    (∑ i ∈ insert (t, true) R, ∑ j ∈ insert (t, true) R,
      futureMatrix r o₁ o₂ q B (insert (t, true) R) (U.erase t) s i j * hᵦ i * hᵦ j) =
    ∑ i ∈ R, ∑ j ∈ R, futureMatrix r o₁ o₂ q B R U s i j * h i * h j
  potential : ∀ (B R : PairedSet n) (U : Finset (Fin n)) (t : Fin n), t ∈ U →
    (∀ c : Bool, (t, c) ∉ B ∧ (t, c) ∉ R) →
    ∀ W h hₐ hᵦ : PairedGround n → ℝ,
    (∀ i ∈ R, hₐ i = h i) → (∀ i ∈ R, hᵦ i = h i) →
    W (t, false) = W (t, true) →
    let sₐ := slotTotal r o₁ o₂ q B (insert (t, false) R) (U.erase t)
    let sᵦ := slotTotal r o₁ o₂ q B (insert (t, true) R) (U.erase t)
    let u := sₐ (t, false)
    (∑ i ∈ insert (t, false) R, sₐ i * hₐ i ^ 2 / W i) +
      (∑ i ∈ insert (t, true) R, sᵦ i * hᵦ i ^ 2 / W i) =
    (∑ i ∈ R, slotTotal r o₁ o₂ q B R U i * h i ^ 2 / W i) +
      (u * hₐ (t, false) ^ 2 + u * hᵦ (t, true) ^ 2) / W (t, false)

/-- INTERNAL: All conservation identities hold for the actual operational
weights, without matroid promises or the quadratic signature premise.
TEXLINE: main.tex:535-567,628-641 -/
theorem slot_conservation_control (n r : ℕ) (o₁ o₂ : IndependenceOracle n) (q : ℚ) :
    SlotConservationControl n r o₁ o₂ q :=
  ⟨slot_total_split r o₁ o₂ q, new_hole_total_eq r o₁ o₂ q,
    future_form_conserved r o₁ o₂ q, slot_potential_split r o₁ o₂ q⟩

end CountingMatroid.Analysis.DefectSlotConservation
