import CountingMatroid.Analysis.ExchangePathCertificate

set_option autoImplicit false

/-! Cardinality of the symmetric difference with a simple alternating
source-to-sink exchange walk. This argument uses no matroid exchange theorem. -/
namespace CountingMatroid.Analysis.ExchangeWalkCardinality
open CountingMatroid.Model CountingMatroid.Analysis.IntersectionSearch
open CountingMatroid.Analysis.ExchangePathCertificate

/-- INTERNAL: A list of distinct toggles removes its original inside vertices
and adds its original outside vertices, with no double toggles. -/
theorem toggle_card_balance {n : ℕ} (p : List (Fin n)) (I : Finset (Fin n))
    (hp : p.Nodup) :
    (p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I).card +
      (p.filter (fun i => decide (i ∈ I))).length =
    I.card + (p.filter (fun i => decide (i ∉ I))).length := by
  classical
  induction p generalizing I with
  | nil => simp
  | cons i p ih =>
    obtain ⟨hi, hp⟩ := List.nodup_cons.mp hp
    by_cases hiI : i ∈ I
    · have hinside : p.filter (fun j => decide (j ∈ I.erase i)) =
          p.filter (fun j => decide (j ∈ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have houtside : p.filter (fun j => decide (j ∉ I.erase i)) =
          p.filter (fun j => decide (j ∉ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have h := ih (I.erase i) hp
      rw [hinside, houtside] at h
      have hcard := Finset.card_erase_add_one hiI
      simp only [List.foldl_cons, List.filter_cons, hiI, not_true_eq_false, decide_true, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons] 
      omega
    · have hinside : p.filter (fun j => decide (j ∈ insert i I)) =
          p.filter (fun j => decide (j ∈ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have houtside : p.filter (fun j => decide (j ∉ insert i I)) =
          p.filter (fun j => decide (j ∉ I)) := by
        apply List.filter_congr
        intro j hj
        have hji : j ≠ i := by rintro rfl; exact hi hj
        simp [hji]
      have h := ih (insert i I) hp
      rw [hinside, houtside, Finset.card_insert_of_notMem hiI] at h
      simp only [List.foldl_cons, List.filter_cons, hiI, not_false_eq_true, decide_true, decide_false, Bool.false_eq_true,
        ↓reduceIte, List.length_cons]
      omega

/-- INTERNAL: An exchange walk alternates outside and inside the original
independent set, starting outside. Its imbalance is determined by its head. -/
theorem source_walk_card_balance {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) {p : List (Fin n)}
    (hw : SourceWalk (buildGraph o₁ o₂ I).val p) :
    ∀ v tail, p = v :: tail →
      (p.filter (fun i => decide (i ∉ I))).length =
        (p.filter (fun i => decide (i ∈ I))).length + (if v ∈ I then 0 else 1) := by
  classical
  induction hw with
  | source v hs =>
    intro w tail heq
    obtain ⟨hvw, hrest⟩ := List.cons.inj heq
    subst w
    subst tail
    have ht := testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂ I v
    have hv : v ∉ I := by
      have : v ∉ I ∧ M₁.Indep (insert v (I : Set (Fin n))) := by
        simpa only [buildGraph_val, ht, decide_eq_true_eq] using hs
      exact this.1
    simp [hv]
  | step u v tail hw he ih =>
    intro w rest heq
    obtain ⟨hvw, hrest⟩ := List.cons.inj heq
    subst w
    subst rest
    have h := ih u tail rfl
    have hedge := testEdge_val M₁ M₂ o₁ o₂ h₁ h₂ I u v
    have he' : (u ∈ I ∧ v ∉ I ∧ M₁.Indep
        (insert v ((I.erase u : Finset (Fin n)) : Set (Fin n)))) ∨
        (u ∉ I ∧ v ∈ I ∧ M₂.Indep
        (insert u ((I.erase v : Finset (Fin n)) : Set (Fin n)))) := by
      simpa only [buildGraph_val, hedge, decide_eq_true_eq] using he
    rcases he' with ⟨hu, hv, _⟩ | ⟨hu, hv, _⟩
    · simp only [List.filter_cons, hu, hv, not_false_eq_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, Nat.add_zero] at h ⊢
      omega
    · simp only [List.filter_cons, hu, hv, not_false_eq_true, not_true_eq_false,
        decide_true, decide_false, Bool.false_eq_true, ↓reduceIte,
        List.length_cons, Nat.add_zero] at h ⊢
      omega

/-- INTERNAL: A simple augmenting walk adds one element more than it removes.
TEXLINE: main.tex:283-289 -/
theorem augmenting_walk_cardinality {n : ℕ} (M₁ M₂ : Matroid (Fin n))
    (o₁ o₂ : IndependenceOracle n) (h₁ : ExactOracle M₁ o₁)
    (h₂ : ExactOracle M₂ o₂) (I : Finset (Fin n)) (p : List (Fin n))
    (hw : AugmentingWalk (buildGraph o₁ o₂ I).val p) (hp : p.Nodup) :
    (p.foldl (fun J i => if i ∈ J then J.erase i else insert i J) I).card =
      I.card + 1 := by
  classical
  have hcard := toggle_card_balance p I hp
  obtain ⟨v, tail, heq, ht⟩ := hw.2
  have hterminal := testTerminal_val M₁ M₂ o₁ o₂ h₁ h₂ I v
  have hv : v ∉ I := by
    have : v ∉ I ∧ M₂.Indep (insert v (I : Set (Fin n))) := by
      simpa only [buildGraph_val, hterminal, decide_eq_true_eq] using ht
    exact this.1
  have hbalance := source_walk_card_balance M₁ M₂ o₁ o₂ h₁ h₂ I hw.1 v tail heq
  rw [if_neg hv] at hbalance
  omega

end CountingMatroid.Analysis.ExchangeWalkCardinality
