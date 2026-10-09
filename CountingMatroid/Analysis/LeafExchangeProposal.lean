import CountingMatroid.Analysis.LeafCliqueFlow
import CountingMatroid.Analysis.ExchangeProposalGeometry

set_option autoImplicit false

/-!
Every pair of distinct terminal leaf vertices is joined by a label swap.
The two orientations of that swap give proposal probability at least
1/(2n²), independently of any matroid representation or rank weight.
-/

namespace CountingMatroid.Analysis.LeafExchangeProposal

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.IdealExchangeChain
open CountingMatroid.Analysis.ExchangeProposalGeometry
open CountingMatroid.Analysis.LeafCliqueFlow

/-- INTERNAL: Both orientations of a nontrivial label swap contribute to
its uniform-label proposal probability.
TEXLINE: main.tex:746-751 -/
theorem exchange_proposal_lower_of_swap (n : ℕ) (hn : 0 < n)
    (state next : PairedSet n) (a b : PairedGround n) (hab : a ≠ b)
    (hswap : exchangeState a b state = next) :
    1 / (2 * (n : ℝ) ^ 2) ≤ exchangeProposal n hn state next := by
  classical
  let c : ℝ := 1 / (Fintype.card (PairedGround n) : ℝ) ^ 2
  let T := fun x y : PairedGround n => if exchangeState x y state = next then c else 0
  have hnn : ∀ x y, 0 ≤ T x y := by
    intro x y
    dsimp only [T]
    split_ifs
    · dsimp only [c]
      positivity
    · exact le_rfl
  have hreverse : exchangeState b a state = next := by
    simpa only [exchangeState, Equiv.swap_comm] using hswap
  have ha : c ≤ ∑ y, T a y := by
    have hh := Finset.single_le_sum (fun y _ => hnn a y) (Finset.mem_univ b)
    simpa only [T, if_pos hswap] using hh
  have hb : c ≤ ∑ y, T b y := by
    have hh := Finset.single_le_sum (fun y _ => hnn b y) (Finset.mem_univ a)
    simpa only [T, if_pos hreverse] using hh
  have hrows : 2 * c ≤ ∑ x ∈ ({a, b} : Finset (PairedGround n)), ∑ y, T x y := by
    rw [Finset.sum_insert (by simpa using hab), Finset.sum_singleton]
    linarith
  have htotal : (∑ x ∈ ({a, b} : Finset (PairedGround n)), ∑ y, T x y) ≤
      ∑ x, ∑ y, T x y := by
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    intro x _ _
    exact Finset.sum_nonneg (fun y _ => hnn x y)
  have heq : 2 * c = 1 / (2 * (n : ℝ) ^ 2) := by
    simp only [c, PairedGround, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_bool, Nat.cast_mul, Nat.cast_ofNat]
    have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
    field_simp
    <;> ring
  rw [← heq]
  exact hrows.trans htotal

/-- PAPER: main.tex:674,746-751
Distinct holes at a terminal node yield an actual exchange with proposal
probability at least one over twice the squared original ground size. -/
theorem leaf_exchange_proposal_lower (n : ℕ) (hn : 0 < n) (B R : PairedSet n)
    (hBR : Disjoint B R) (x y : R) (hxy : x ≠ y) :
    1 / (2 * (n : ℝ) ^ 2) ≤
      exchangeProposal n hn (leafVertex B R x) (leafVertex B R y) := by
  classical
  have hne : x.val ≠ y.val := fun he => hxy (Subtype.ext he)
  have hxB : x.val ∉ B := fun hh => Finset.disjoint_left.mp hBR hh x.property
  have hyB : y.val ∉ B := fun hh => Finset.disjoint_left.mp hBR hh y.property
  have hy : y.val ∈ leafVertex B R x :=
    Finset.mem_union_right _ (Finset.mem_erase.mpr ⟨hne.symm, y.property⟩)
  have hx : x.val ∉ leafVertex B R x := by simp [leafVertex, hxB]
  apply exchange_proposal_lower_of_swap n hn _ _ y.val x.val hne.symm
  rw [exchange_state_erase_insert _ _ _ hy hx]
  ext e
  simp only [Finset.mem_insert, leafVertex, Finset.mem_erase, Finset.mem_union]
  by_cases hex : e = x.val
  · subst e
    simp [hne, x.property, hxB]
  · by_cases hey : e = y.val
    · subst e
      simp [hyB, hne.symm]
    · simp [hex, hey]

/-- INTERNAL: Normalize the terminal vertex capacities against the
operational exchange conductance, retaining the exact factor 2n²Z.
TEXLINE: main.tex:721-728,746-751,875-898 -/
theorem scaled_leaf_conductance_lower (n : ℕ) (hn : 0 < n)
    (B R : PairedSet n) (hBR : Disjoint B R) (π : PairedSet n → ℝ)
    (hπ : ∀ state, 0 ≤ π state) (Z : ℝ) (hZ : 0 < Z) (c : R → ℝ)
    (hvertex : ∀ hole, c hole = Z * π (leafVertex B R hole))
    (x y : R) (hxy : x ≠ y) :
    min (c x) (c y) ≤ (2 * (n : ℝ) ^ 2 * Z) *
      (exchangeProposal n hn (leafVertex B R x) (leafVertex B R y) *
        min (π (leafVertex B R x)) (π (leafVertex B R y))) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  let m := min (π (leafVertex B R x)) (π (leafVertex B R y))
  have hm : 0 ≤ m := le_min (hπ _) (hπ _)
  have hp := mul_le_mul_of_nonneg_right
    (leaf_exchange_proposal_lower n hn B R hBR x y hxy) hm
  have hC : 0 ≤ 2 * (n : ℝ) ^ 2 * Z := by positivity
  calc
    min (c x) (c y) = Z * m := by
      rw [hvertex x, hvertex y, ← mul_min_of_nonneg _ _ hZ.le]
    _ = (2 * (n : ℝ) ^ 2 * Z) * ((1 / (2 * (n : ℝ) ^ 2)) * m) := by
      field_simp
    _ ≤ _ := mul_le_mul_of_nonneg_left hp hC

end CountingMatroid.Analysis.LeafExchangeProposal
