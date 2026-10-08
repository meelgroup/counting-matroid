import CountingMatroid.Analysis.IdealExchangeChain

set_option autoImplicit false

namespace CountingMatroid.Analysis.ExchangeProposalGeometry

open CountingMatroid.Model CountingMatroid.Analysis.IdealExchangeChain

/-- INTERNAL: A label swap fixes a paired subset when both labels have the
same occupancy. This identifies the holding proposals in the ideal chain.
TEXLINE: main.tex:746-751 -/
theorem exchange_state_same_occupancy {n : ℕ} (state : PairedSet n)
    (a b : PairedGround n) (h : a ∈ state ↔ b ∈ state) :
    exchangeState a b state = state := by
  classical
  ext x
  simp only [exchangeState, Finset.mem_image]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases ha : y = a
    · subst y
      simpa only [Equiv.swap_apply_left] using h.mp hy
    by_cases hb : y = b
    · subst y
      simpa only [Equiv.swap_apply_right] using h.mpr hy
    simpa only [Equiv.swap_apply_of_ne_of_ne ha hb] using hy
  · intro hx
    refine ⟨Equiv.swap a b x, ?_, Equiv.swap_apply_self a b x⟩
    by_cases ha : x = a
    · subst x
      simpa only [Equiv.swap_apply_left] using h.mp hx
    by_cases hb : x = b
    · subst x
      simpa only [Equiv.swap_apply_right] using h.mpr hx
    simpa only [Equiv.swap_apply_of_ne_of_ne ha hb] using hx

/-- INTERNAL: A label swap with opposite occupancy is exactly the erase/insert
candidate constructed in `Program.chainStep`.
TEXLINE: main.tex:746-751 -/
theorem exchange_state_erase_insert {n : ℕ} (state : PairedSet n)
    (a b : PairedGround n) (ha : a ∈ state) (hb : b ∉ state) :
    exchangeState a b state = insert b (state.erase a) := by
  classical
  have hab : a ≠ b := ne_of_mem_of_not_mem ha hb
  ext x
  simp only [exchangeState, Finset.mem_image, Finset.mem_insert, Finset.mem_erase]
  constructor
  · rintro ⟨y, hy, rfl⟩
    by_cases hya : y = a
    · subst y
      exact Or.inl (Equiv.swap_apply_left a b)
    have hyb : y ≠ b := ne_of_mem_of_not_mem hy hb
    rw [Equiv.swap_apply_of_ne_of_ne hya hyb]
    exact Or.inr ⟨hya, hy⟩
  · intro hx
    rcases hx with hxb | ⟨hxa, hx⟩
    · subst x
      exact ⟨a, ha, Equiv.swap_apply_left a b⟩
    · have hxb : x ≠ b := ne_of_mem_of_not_mem hx hb
      exact ⟨x, hx, Equiv.swap_apply_of_ne_of_ne hxa hxb⟩

/-- INTERNAL: Split the uniform two-label exchange average into its two
holding blocks and twice the occupied/unoccupied exchange block.
TEXLINE: main.tex:746-751 -/
theorem exchange_sum_partition {n : ℕ} (state : PairedSet n)
    (F : PairedSet n → ℝ) :
    (∑ a : PairedGround n, ∑ b : PairedGround n, F (exchangeState a b state)) =
      ((state.card : ℝ) ^ 2 + (stateᶜ.card : ℝ) ^ 2) * F state +
        2 * ∑ a ∈ state, ∑ b ∈ stateᶜ, F (insert b (state.erase a)) := by
  classical
  have hin (a : PairedGround n) (ha : a ∈ state) :
      (∑ b : PairedGround n, F (exchangeState a b state)) =
        (state.card : ℝ) * F state +
          ∑ b ∈ stateᶜ, F (insert b (state.erase a)) := by
    rw [← Finset.sum_add_sum_compl state]
    congr 1
    · rw [Finset.sum_congr rfl (fun b hb =>
        congrArg F (exchange_state_same_occupancy state a b (by simp [ha, hb])))]
      simp
    · apply Finset.sum_congr rfl
      intro b hb
      rw [exchange_state_erase_insert state a b ha (Finset.mem_compl.mp hb)]
  have hout (a : PairedGround n) (ha : a ∈ stateᶜ) :
      (∑ b : PairedGround n, F (exchangeState a b state)) =
        (∑ b ∈ state, F (insert a (state.erase b))) +
          (stateᶜ.card : ℝ) * F state := by
    rw [← Finset.sum_add_sum_compl state]
    congr 1
    · apply Finset.sum_congr rfl
      intro b hb
      rw [exchangeState, Equiv.swap_comm a b]
      change F (exchangeState b a state) = _
      rw [exchange_state_erase_insert state b a hb (Finset.mem_compl.mp ha)]
    · rw [Finset.sum_congr rfl (fun b hb =>
        congrArg F (exchange_state_same_occupancy state a b
          (by simp [Finset.mem_compl.mp ha, Finset.mem_compl.mp hb])))]
      simp
  rw [← Finset.sum_add_sum_compl state,
    Finset.sum_congr rfl hin, Finset.sum_congr rfl hout,
    Finset.sum_add_distrib, Finset.sum_add_distrib]
  have hcross : (∑ a ∈ stateᶜ, ∑ b ∈ state, F (insert a (state.erase b))) =
      ∑ b ∈ state, ∑ a ∈ stateᶜ, F (insert a (state.erase b)) := Finset.sum_comm
  rw [hcross]
  simp only [Finset.sum_const, nsmul_eq_mul]
  ring

/-- INTERNAL: On an n-element state the ideal uniform-label proposal is
exactly one-half holding plus uniformly choosing an occupied and an
unoccupied label, as in the program before acceptance and draw caps.
TEXLINE: main.tex:746-751 -/
theorem exchange_proposal_average (n : ℕ) (hn : 0 < n)
    (state : PairedSet n) (hcard : state.card = n) (F : PairedSet n → ℝ) :
    (∑ next : PairedSet n, exchangeProposal n hn state next * F next) =
      (1 / 2 : ℝ) * F state +
        (1 / (2 * (n : ℝ) ^ 2)) *
          ∑ a ∈ state, ∑ b ∈ stateᶜ, F (insert b (state.erase a)) := by
  classical
  have hsum : (∑ next : PairedSet n, exchangeProposal n hn state next * F next) =
      (∑ a : PairedGround n, ∑ b : PairedGround n, F (exchangeState a b state)) /
        (Fintype.card (PairedGround n) : ℝ) ^ 2 := by
    change (∑ next : PairedSet n,
      (∑ a : PairedGround n, ∑ b : PairedGround n,
        if exchangeState a b state = next then
          1 / (Fintype.card (PairedGround n) : ℝ) ^ 2 else 0) * F next) = _
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    rw [Finset.sum_congr rfl (fun a _ => Finset.sum_comm)]
    simp only [ite_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    simp only [← Finset.mul_sum, div_eq_mul_inv]
    ring
  rw [hsum, exchange_sum_partition, hcard, Finset.card_compl, hcard]
  have hlabels : Fintype.card (PairedGround n) = 2 * n := by
    simp [PairedGround, Nat.mul_comm]
  rw [hlabels, show 2 * n - n = n by omega]
  push_cast
  have hnreal : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp [hnreal]
  ring

/-- INTERNAL: The exchange proposal holds with probability at least one-half
on every n-element state; rejection can only increase this probability.
TEXLINE: main.tex:746-757 -/
theorem exchange_proposal_lazy (n : ℕ) (hn : 0 < n)
    (state : PairedSet n) (hcard : state.card = n) :
    (1 / 2 : ℝ) ≤ exchangeProposal n hn state state := by
  classical
  have hav := exchange_proposal_average n hn state hcard
    (fun next => if next = state then (1 : ℝ) else 0)
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
    Finset.mem_univ, if_true] at hav
  rw [hav]
  apply le_add_of_nonneg_right
  apply mul_nonneg (by positivity)
  apply Finset.sum_nonneg
  intro a _
  apply Finset.sum_nonneg
  intro b _
  split_ifs <;> positivity

/-- INTERNAL: Metropolis rejection preserves the one-half holding bound of
the concrete ideal exchange proposal, even for targets with zero weights.
TEXLINE: main.tex:746-757 -/
theorem ideal_chain_lazy {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (q : ℚ) (w : Multipliers n) (hn : 0 < n) (hq : 0 < q)
    (hw : ∀ index, 0 < w index) (state : PairedSet n)
    (hcard : state.card = n) :
    (1 / 2 : ℝ) ≤ idealChain r o₁ o₂ q w hn hq hw state state := by
  classical
  let π := operationalLaw r o₁ o₂ q w hq hw
  let Q := exchangeProposal n hn
  have hsum : Q state state + ∑ next ∈ Finset.univ.erase state, Q state next = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ state)]
    exact Q.sum_coe state
  have hle : (∑ next ∈ Finset.univ.erase state,
      Arlib.MarkovChains.mhRate π Q state next) ≤
        ∑ next ∈ Finset.univ.erase state, Q state next :=
    Finset.sum_le_sum (fun next _ => Arlib.MarkovChains.mhRate_le_proposal π Q state next)
  have hlazy := exchange_proposal_lazy n hn state hcard
  change (1 / 2 : ℝ) ≤ Arlib.MarkovChains.metropolis π Q state state
  rw [Arlib.MarkovChains.metropolis_apply_self, Arlib.MarkovChains.mhStay]
  linarith

end CountingMatroid.Analysis.ExchangeProposalGeometry
