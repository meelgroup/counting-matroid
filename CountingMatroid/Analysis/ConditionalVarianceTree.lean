import CountingMatroid.Analysis.ConditionalTransversalSplitTransport

set_option autoImplicit false

/-!
Finite binary variance-tree bookkeeping for partial transversal assignments.
The moment and energy identities are independent of coefficient extraction
and the slot-flow construction. They use the concrete conditional sums.
-/

namespace CountingMatroid.Analysis.ConditionalVarianceTree

open CountingMatroid.Model
open CountingMatroid.Analysis.ConditionalDefectCoefficients
open CountingMatroid.Analysis.ConditionalTransversalSplitTransport
open CountingMatroid.Analysis.TransversalPartition
open CountingMatroid.Analysis.ExchangeFlowEnergy

/-- INTERNAL: Extend the conditional unmultiplied weights by zero outside
the assignment event, on the original-subset indexing of transversals.
TEXLINE: main.tex:832-839 -/
noncomputable def nodeWeight {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (A : Finset (Fin n)) : ℝ := by
  classical
  exact if SubsetRespects σ A then (q ^ transversalDeficiency r o₁ o₂ A : ℚ) else 0

/-- INTERNAL: The real node weights sum to the already defined rational
conditional transversal total.
TEXLINE: main.tex:832-839 -/
theorem sum_node_weight {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) :
    (∑ A, nodeWeight r o₁ o₂ q σ A) = (transversalTotal r o₁ o₂ q σ : ℝ) := by
  classical
  simp only [nodeWeight, transversalTotal, Rat.cast_sum, apply_ite, Rat.cast_zero]

/-- INTERNAL: Write the conditional mean as a weighted first moment.
TEXLINE: main.tex:832-839 -/
theorem conditional_mean_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (H : PairedSet n → ℝ) :
    conditionalMean r o₁ o₂ q σ H =
      (∑ A, nodeWeight r o₁ o₂ q σ A * H (transversalState A)) /
        (transversalTotal r o₁ o₂ q σ : ℝ) := by
  classical
  unfold conditionalMean
  congr 1
  apply Finset.sum_congr rfl
  intro A _
  dsimp only [nodeWeight]
  split_ifs <;> simp

/-- INTERNAL: Write the conditional moment using weights extended by zero.
TEXLINE: main.tex:832-839 -/
theorem conditional_moment_eq {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (H : PairedSet n → ℝ) :
    conditionalMoment r o₁ o₂ q σ H =
      ∑ A, nodeWeight r o₁ o₂ q σ A *
        (H (transversalState A) - conditionalMean r o₁ o₂ q σ H) ^ 2 := by
  classical
  unfold conditionalMoment
  apply Finset.sum_congr rfl
  intro A _
  dsimp only [nodeWeight]
  split_ifs <;> simp

/-- INTERNAL: Expand a finite weighted centered moment. The weights need
not sum to one; only the positive total is divided out.
TEXLINE: main.tex:832-839 -/
theorem weighted_moment_expansion {α : Type*} [Fintype α] (w x : α → ℝ)
    (s : ℝ) (hs : s ≠ 0) (hws : (∑ i, w i) = s) :
    (∑ i, w i * (x i - (∑ j, w j * x j) / s) ^ 2) =
      (∑ i, w i * (x i) ^ 2) - (∑ i, w i * x i) ^ 2 / s := by
  let m := (∑ i, w i * x i) / s
  have he : (∑ i, w i * (x i - m) ^ 2) =
      (∑ i, w i * x i ^ 2) - 2 * m * (∑ i, w i * x i) + m ^ 2 * (∑ i, w i) := by
    calc
      _ = ∑ i, (w i * x i ^ 2 - (2 * m) * (w i * x i) + m ^ 2 * w i) := by
        apply Finset.sum_congr rfl
        intro i _
        ring
      _ = _ := by
        simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rw [he, hws]
  dsimp only [m]
  field_simp [hs]
  ring

/-- INTERNAL: The conditional second moment minus its squared first moment
is exactly the unnormalized variance at the node.
TEXLINE: main.tex:832-839 -/
theorem conditional_moment_expansion {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) (H : PairedSet n → ℝ) :
    conditionalMoment r o₁ o₂ q σ H =
      (∑ A, nodeWeight r o₁ o₂ q σ A * H (transversalState A) ^ 2) -
        (∑ A, nodeWeight r o₁ o₂ q σ A * H (transversalState A)) ^ 2 /
          (transversalTotal r o₁ o₂ q σ : ℝ) := by
  rw [conditional_moment_eq, conditional_mean_eq]
  have hs : (0 : ℝ) < transversalTotal r o₁ o₂ q σ := by
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ
  exact weighted_moment_expansion _ _ _ hs.ne' (sum_node_weight r o₁ o₂ q σ)

/-- INTERNAL: A node weight partitions pointwise over its two children.
TEXLINE: main.tex:832-839 -/
theorem node_weight_split {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (σ : Assignment n) (k : Fin n) (hk : σ k = none) (A : Finset (Fin n)) :
    nodeWeight r o₁ o₂ q (Function.update σ k (some false)) A +
      nodeWeight r o₁ o₂ q (Function.update σ k (some true)) A =
        nodeWeight r o₁ o₂ q σ A := by
  classical
  unfold nodeWeight
  rw [subset_respects_update σ k hk false A, subset_respects_update σ k hk true A]
  by_cases hA : SubsetRespects σ A <;> by_cases hmem : k ∈ A <;> simp [hA, hmem]

/-- PAPER: main.tex:832-834
Unnormalized binary variance decomposition at one conditioning node. -/
theorem conditional_moment_split {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) (k : Fin n) (hk : σ k = none)
    (H : PairedSet n → ℝ) :
    conditionalMoment r o₁ o₂ q σ H =
      conditionalMoment r o₁ o₂ q (Function.update σ k (some false)) H +
      conditionalMoment r o₁ o₂ q (Function.update σ k (some true)) H +
      ((transversalTotal r o₁ o₂ q (Function.update σ k (some false)) : ℝ) *
        (transversalTotal r o₁ o₂ q (Function.update σ k (some true)) : ℝ) /
        (transversalTotal r o₁ o₂ q σ : ℝ)) *
      (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
        conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 := by
  classical
  let σ₀ := Function.update σ k (some false)
  let σ₁ := Function.update σ k (some true)
  let s₀ : ℝ := transversalTotal r o₁ o₂ q σ₀
  let s₁ : ℝ := transversalTotal r o₁ o₂ q σ₁
  let z : ℝ := transversalTotal r o₁ o₂ q σ
  let F := fun τ : Assignment n => ∑ A, nodeWeight r o₁ o₂ q τ A * H (transversalState A)
  let Q := fun τ : Assignment n => ∑ A, nodeWeight r o₁ o₂ q τ A * H (transversalState A) ^ 2
  have hs₀ : 0 < s₀ := by
    dsimp only [s₀]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ₀
  have hs₁ : 0 < s₁ := by
    dsimp only [s₁]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ₁
  have hsplit : s₀ + s₁ = z := by
    dsimp only [s₀, s₁, z, σ₀, σ₁]
    exact_mod_cast transversal_total_split r o₁ o₂ q σ k hk
  have hfirst : F σ₀ + F σ₁ = F σ := by
    simp only [F, σ₀, σ₁, ← Finset.sum_add_distrib, ← add_mul, node_weight_split r o₁ o₂ q σ k hk]
  have hsecond : Q σ₀ + Q σ₁ = Q σ := by
    simp only [Q, σ₀, σ₁, ← Finset.sum_add_distrib, ← add_mul, node_weight_split r o₁ o₂ q σ k hk]
  rw [conditional_moment_expansion r o₁ o₂ q hq σ H,
    conditional_moment_expansion r o₁ o₂ q hq σ₀ H,
    conditional_moment_expansion r o₁ o₂ q hq σ₁ H,
    conditional_mean_eq r o₁ o₂ q σ₀ H, conditional_mean_eq r o₁ o₂ q σ₁ H]
  change Q σ - F σ ^ 2 / z = Q σ₀ - F σ₀ ^ 2 / s₀ +
    (Q σ₁ - F σ₁ ^ 2 / s₁) + (s₀ * s₁ / z) * (F σ₀ / s₀ - F σ₁ / s₁) ^ 2
  rw [← hfirst, ← hsecond, ← hsplit]
  field_simp [hs₀.ne', hs₁.ne', (add_pos hs₀ hs₁).ne']
  ring

/-- INTERNAL: Conditioning a paired state at an unassigned pair adds its
inclusion/exclusion test to the existing assignment predicate.
TEXLINE: main.tex:834-838 -/
theorem respects_update {n : ℕ} (σ : Assignment n) (k : Fin n) (hk : σ k = none)
    (b : Bool) (state : PairedSet n) :
    Respects (Function.update σ k (some b)) state ↔
      Respects σ state ∧ ((k, b) ∈ state ∧ (k, !b) ∉ state) := by
  classical
  constructor
  · intro h
    refine ⟨?_, h k b (by simp)⟩
    intro i a hi
    have hik : i ≠ k := by rintro rfl; rw [hk] at hi; cases hi
    apply h i a
    simpa [Function.update_of_ne hik] using hi
  · rintro ⟨h, hb⟩ i a hi
    by_cases hik : i = k
    · subst i
      have hab : b = a := by simpa using hi
      simpa [← hab] using hb
    · apply h i a
      simpa [Function.update_of_ne hik] using hi

/-- PAPER: main.tex:834-838
The two children's endpoint sets are disjoint, so their restricted energies
sum to at most the parent's energy, even for invalid or zero-weight states. -/
theorem node_energy_split_le {n : ℕ} (κ : PairedSet n → PairedSet n → ℝ)
    (hκ : ∀ state next, 0 ≤ κ state next) (H : PairedSet n → ℝ)
    (σ : Assignment n) (k : Fin n) (hk : σ k = none) :
    nodeEnergy κ H (Function.update σ k (some false)) +
      nodeEnergy κ H (Function.update σ k (some true)) ≤ nodeEnergy κ H σ := by
  classical
  simp only [nodeEnergy, ← mul_add, ← Finset.sum_add_distrib]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  apply Finset.sum_le_sum
  intro state _
  apply Finset.sum_le_sum
  intro next _
  rw [respects_update σ k hk false state, respects_update σ k hk false next,
    respects_update σ k hk true state, respects_update σ k hk true next]
  have hnonneg := mul_nonneg (hκ state next) (sq_nonneg (H state - H next))
  by_cases hS : Respects σ state <;> by_cases hN : Respects σ next
  all_goals simp only [hS, hN, true_and, false_and, and_false, if_false]
  all_goals try norm_num
  by_cases hs₀ : (k, false) ∈ state <;> by_cases hs₁ : (k, true) ∈ state <;>
    by_cases hn₀ : (k, false) ∈ next <;> by_cases hn₁ : (k, true) ∈ next <;>
      simp [hs₀, hs₁, hn₀, hn₁, hnonneg]

/-- INTERNAL: The unassigned pairs measure the remaining height of any
adaptive conditioning tree.
TEXLINE: main.tex:834-839 -/
noncomputable def unassigned {n : ℕ} (σ : Assignment n) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i => σ i = none)

/-- INTERNAL: Assigning an unassigned pair removes exactly that pair from
the remaining-height measure.
TEXLINE: main.tex:834-839 -/
theorem unassigned_update {n : ℕ} (σ : Assignment n) (k : Fin n) (b : Bool) :
    unassigned (Function.update σ k (some b)) = (unassigned σ).erase k := by
  classical
  ext i
  by_cases hik : i = k
  · subst i; simp [unassigned]
  · simp [unassigned, hik]

/-- INTERNAL: A fully assigned node has only one transversal, so its
conditional centered moment is zero.
TEXLINE: main.tex:833-834 -/
theorem fully_assigned_moment_zero {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (hq : 0 < q) (σ : Assignment n) (H : PairedSet n → ℝ)
    (hfull : ∀ i, σ i ≠ none) : conditionalMoment r o₁ o₂ q σ H = 0 := by
  classical
  let A₀ := Finset.univ.filter (fun i => σ i = some false)
  have hA₀ : SubsetRespects σ A₀ := by
    intro i b hb
    cases b <;> simp [A₀, hb]
  have hunique (A : Finset (Fin n)) (hA : SubsetRespects σ A) : A = A₀ := by
    ext i
    cases hi : σ i with
    | none => exact False.elim (hfull i hi)
    | some b =>
      have hd : decide (i ∉ A) = decide (i ∉ A₀) := (hA i b hi).trans (hA₀ i b hi).symm
      have he : (i ∉ A) ↔ (i ∉ A₀) := by simpa only [decide_eq_decide] using hd
      simpa only [not_not] using not_congr he
  have hfirst : (∑ A, nodeWeight r o₁ o₂ q σ A * H (transversalState A)) =
      (transversalTotal r o₁ o₂ q σ : ℝ) * H (transversalState A₀) := by
    rw [← sum_node_weight r o₁ o₂ q σ, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro A _
    by_cases hA : SubsetRespects σ A
    · rw [hunique A hA]
    · simp [nodeWeight, hA]
  have hs : (0 : ℝ) < transversalTotal r o₁ o₂ q σ := by
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ
  have hmean : conditionalMean r o₁ o₂ q σ H = H (transversalState A₀) := by
    rw [conditional_mean_eq, hfirst]
    field_simp
  rw [conditional_moment_eq, hmean]
  apply Finset.sum_eq_zero
  intro A _
  by_cases hA : SubsetRespects σ A
  · rw [hunique A hA]
    simp
  · simp [nodeWeight, hA]

/-- INTERNAL: Restricting endpoints preserves nonnegativity of potential
energy under nonnegative conductances.
TEXLINE: main.tex:834-839 -/
theorem node_energy_nonneg {n : ℕ} (κ : PairedSet n → PairedSet n → ℝ)
    (hκ : ∀ state next, 0 ≤ κ state next) (H : PairedSet n → ℝ) (σ : Assignment n) :
    0 ≤ nodeEnergy κ H σ := by
  apply mul_nonneg (by norm_num)
  apply Finset.sum_nonneg
  intro state _
  apply Finset.sum_nonneg
  intro next _
  split_ifs
  · exact mul_nonneg (hκ _ _) (sq_nonneg _)
  · exact le_rfl

/-- PAPER: main.tex:832-839
Adaptive binary variance decomposition charges at most one restricted
energy per remaining depth. The selected split can vary from node to node. -/
theorem adaptive_conditional_moment_bound {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (q : ℚ) (hq : 0 < q)
    (κ : PairedSet n → PairedSet n → ℝ) (hκ : ∀ state next, 0 ≤ κ state next)
    (H : PairedSet n → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hnode : ∀ σ : Assignment n, (∃ i, σ i = none) →
      ∃ k, σ k = none ∧
        ((transversalTotal r o₁ o₂ q (Function.update σ k (some false)) : ℝ) *
          (transversalTotal r o₁ o₂ q (Function.update σ k (some true)) : ℝ) /
          (transversalTotal r o₁ o₂ q σ : ℝ)) *
        (conditionalMean r o₁ o₂ q (Function.update σ k (some false)) H -
          conditionalMean r o₁ o₂ q (Function.update σ k (some true)) H) ^ 2 ≤
            K * nodeEnergy κ H σ) (σ : Assignment n) :
    conditionalMoment r o₁ o₂ q σ H ≤
      ((unassigned σ).card : ℝ) * K * nodeEnergy κ H σ := by
  classical
  suffices hmain : ∀ m : ℕ, ∀ τ : Assignment n, (unassigned τ).card = m →
      conditionalMoment r o₁ o₂ q τ H ≤ (m : ℝ) * K * nodeEnergy κ H τ by
    exact hmain _ σ rfl
  intro m
  induction m using Nat.strong_induction_on with
  | h m ih =>
    intro τ hm
    by_cases hremaining : ∃ i, τ i = none
    · obtain ⟨k, hk, hsplit⟩ := hnode τ hremaining
      let τ₀ := Function.update τ k (some false)
      let τ₁ := Function.update τ k (some true)
      let l := (unassigned τ₀).card
      have hk' : k ∈ unassigned τ := by simp [unassigned, hk]
      have hmplus : m = l + 1 := by
        dsimp only [l, τ₀]
        rw [unassigned_update, Finset.card_erase_of_mem hk', hm]
        have hmpos : 0 < m := by rw [← hm]; exact Finset.card_pos.mpr ⟨k, hk'⟩
        omega
      have hcard₁ : (unassigned τ₁).card = l := by
        dsimp only [τ₁, l, τ₀]
        rw [unassigned_update, unassigned_update]
      have hl : l < m := by omega
      have hi₀ := ih l hl τ₀ rfl
      have hi₁ := ih l hl τ₁ hcard₁
      have henergy := node_energy_split_le κ hκ H τ k hk
      rw [conditional_moment_split r o₁ o₂ q hq τ k hk H]
      calc
        _ ≤ (l : ℝ) * K * nodeEnergy κ H τ₀ +
          (l : ℝ) * K * nodeEnergy κ H τ₁ + K * nodeEnergy κ H τ :=
            add_le_add (add_le_add hi₀ hi₁) hsplit
        _ = (l : ℝ) * K * (nodeEnergy κ H τ₀ + nodeEnergy κ H τ₁) +
          K * nodeEnergy κ H τ := by ring
        _ ≤ (l : ℝ) * K * nodeEnergy κ H τ + K * nodeEnergy κ H τ := by
          exact add_le_add
            (mul_le_mul_of_nonneg_left henergy (mul_nonneg (Nat.cast_nonneg l) hK)) le_rfl
        _ = (m : ℝ) * K * nodeEnergy κ H τ := by rw [hmplus]; push_cast; ring
    · have hfull : ∀ i, τ i ≠ none := by simpa only [not_exists] using hremaining
      rw [fully_assigned_moment_zero r o₁ o₂ q hq τ H hfull]
      exact mul_nonneg (mul_nonneg (Nat.cast_nonneg m) hK) (node_energy_nonneg κ hκ H τ)

/-- INTERNAL: Evaluate the existing classifier on an encoded transversal.
Only its forward implication is needed for the general finite reindexing.
TEXLINE: main.tex:270-281,832-839 -/
theorem transversal_state_classified {n : ℕ} (A : Finset (Fin n)) :
    (CountingMatroid.Program.classifyState (transversalState A)).val = .transversal := by
  classical
  let step := fun (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) => do
    let x ← CountingMatroid.Model.Operations.containsPaired (transversalState A) (i, false)
    let y ← CountingMatroid.Model.Operations.containsPaired (transversalState A) (i, true)
    if x then
      if y then
        let seen ← CountingMatroid.Model.Operations.isSome acc.2.1
        if seen then pure (acc.1, acc.2.1, true)
        else pure (acc.1, some i, acc.2.2)
      else pure acc
    else
      if y then pure acc
      else
        let seen ← CountingMatroid.Model.Operations.isSome acc.1
        if seen then pure (acc.1, acc.2.1, true)
        else pure (some i, acc.2.1, acc.2.2)
  have hstep (acc : Option (Fin n) × Option (Fin n) × Bool) (i : Fin n) :
      (step acc i).val = acc := by
    by_cases hi : i ∈ A <;>
      simp [step, CountingMatroid.Model.Operations.containsPaired, transversalState, hi]
  have hfold (l : List (Fin n)) (acc : Option (Fin n) × Option (Fin n) × Bool) :
      (Arlib.Computation.Charged.foldl step l acc).val = acc := by
    induction l generalizing acc with
    | nil => rfl
    | cons i l ih => rw [Arlib.Computation.Charged.val_foldl_cons, hstep, ih]
  unfold CountingMatroid.Program.classifyState
  change ((do
    let result ← Arlib.Computation.Charged.foldl step (List.finRange n) (none, none, false)
    if result.2.2 then pure .invalid else
      match result.1, result.2.1 with
      | none, none => pure .transversal
      | some i, some j => do
          let diagonal ← CountingMatroid.Model.Operations.indexEqual i j
          if diagonal then pure .invalid else pure (.defect i j)
      | _, _ => pure .invalid) :
        Arlib.Computation.Charged CountingMatroid.Model.Operations.Op
          CountingMatroid.Model.Operations.Cell (StateKind n)).val = _
  simp [hfold]

/-- INTERNAL: Reindex any function on the operational transversal fiber,
extending the existing partition-sum identity to observables. Surjectivity
uses the already proved fiber cardinality rather than a second scan invariant.
TEXLINE: main.tex:270-281,832-839 -/
theorem transversal_sum_reindex {n : ℕ} (f : PairedSet n → ℝ) :
    (∑ state : PairedSet n, if (CountingMatroid.Program.classifyState state).val =
      .transversal then f state else 0) = ∑ A : Finset (Fin n), f (transversalState A) := by
  classical
  let T := Finset.univ.filter (fun state : PairedSet n =>
    (CountingMatroid.Program.classifyState state).val = .transversal)
  have hinj : Function.Injective (transversalState (n := n)) := by
    intro A B h
    have hp := congrArg (fun state : PairedSet n =>
      (CountingMatroid.Model.Subroutines.pairedProjections state).val.1) h
    simpa only [transversalState, TransversalProjection.pairedProjections_transversal] using hp
  have hsubset : (Finset.univ.image (transversalState (n := n))) ⊆ T := by
    intro state hs
    obtain ⟨A, _, rfl⟩ := Finset.mem_image.mp hs
    simp [T, transversal_state_classified]
  have hcard : T.card = (Finset.univ : Finset (Finset (Fin n))).card := by
    have h := TransversalClassPartition.transversal_class_partition (n := n)
      0 (fun _ => false) (fun _ => false) 1
    have h' : (T.card : ℚ) = ((Finset.univ : Finset (Finset (Fin n))).card : ℚ) := by
      simpa only [T, partitionSum, one_pow, ← Finset.sum_filter,
        Finset.sum_const, nsmul_eq_mul, mul_one] using h
    exact_mod_cast h'
  have himage : (Finset.univ.image (transversalState (n := n))) = T :=
    Finset.eq_of_subset_of_card_le hsubset (by rw [Finset.card_image_of_injective _ hinj, hcard])
  rw [← Finset.sum_filter]
  change (∑ state ∈ T, f state) = _
  rw [← himage, Finset.sum_image]
  intro A _ B _ h
  exact hinj h

/-- INTERNAL: Identify the root's unnormalized transversal moment with the
operational law's classifier-based centered moment, retaining the normalizer.
TEXLINE: main.tex:832-839 -/
theorem root_conditional_moment {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hq : 0 < q) (hw : ∀ index, 0 < w index)
    (H : PairedSet n → ℝ) :
    let π := IdealExchangeChain.operationalLaw r o₁ o₂ q w hq hw
    conditionalMoment r o₁ o₂ q (fun _ => none) H =
      (StationaryMeanIdentities.normalizer r o₁ o₂ q w : ℝ) *
        (∑ state : PairedSet n, if (CountingMatroid.Program.classifyState state).val =
          .transversal then π state *
            (H state - ObservableVarianceDecomposition.classMean π H .transversal) ^ 2 else 0) := by
  classical
  intro π
  let Z : ℝ := StationaryMeanIdentities.normalizer r o₁ o₂ q w
  let σ : Assignment n := fun _ => none
  let z : ℝ := transversalTotal r o₁ o₂ q σ
  have hZ : 0 < Z := by
    dsimp only [Z]
    exact_mod_cast (StationaryMeanIdentities.stationary_mean_identities r o₁ o₂ q 1 w hq hw).1
  have hz : 0 < z := by
    dsimp only [z]
    exact_mod_cast transversal_total_pos r o₁ o₂ q hq σ
  have hweight (A : Finset (Fin n)) :
      π (transversalState A) = nodeWeight r o₁ o₂ q σ A / Z := by
    simp [π, IdealExchangeChain.operationalLaw, StationaryMeanIdentities.stateWeight,
      transversal_state_classified, CountingMatroid.Program.weightOfKind,
      CountingMatroid.Model.Operations.natSub,
      BoundedRunResourceEnvelope.ratPower_value, nodeWeight, SubsetRespects, σ, Z,
      transversalDeficiency]
  have hmass : ObservableVarianceDecomposition.classMass π .transversal = z / Z := by
    unfold ObservableVarianceDecomposition.classMass
    rw [transversal_sum_reindex]
    simp_rw [hweight]
    rw [← Finset.sum_div, sum_node_weight]
  have hfirst : (∑ state : PairedSet n,
      if (CountingMatroid.Program.classifyState state).val = .transversal then
        π state * H state else 0) =
      (∑ A, nodeWeight r o₁ o₂ q σ A * H (transversalState A)) / Z := by
    rw [transversal_sum_reindex]
    simp_rw [hweight, div_mul_eq_mul_div]
    rw [← Finset.sum_div]
  have hmean : ObservableVarianceDecomposition.classMean π H .transversal =
      conditionalMean r o₁ o₂ q σ H := by
    unfold ObservableVarianceDecomposition.classMean
    rw [hfirst, hmass, conditional_mean_eq]
    change _ = _ / z
    field_simp [hZ.ne', hz.ne']
  rw [conditional_moment_eq, transversal_sum_reindex]
  simp_rw [hweight, hmean]
  change _ = Z * _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro A _
  field_simp [hZ.ne']
  rfl

/-- INTERNAL: The empty assignment restricts no endpoints, so its energy
is the full potential energy.
TEXLINE: main.tex:834-839 -/
theorem node_energy_empty {n : ℕ} (κ : PairedSet n → PairedSet n → ℝ)
    (H : PairedSet n → ℝ) : nodeEnergy κ H (fun _ => none) = potentialEnergy κ H := by
  classical
  simp only [nodeEnergy, Respects, reduceCtorEq, forall_const, false_implies,
    implies_true, and_self, if_true, potentialEnergy]

end CountingMatroid.Analysis.ConditionalVarianceTree
