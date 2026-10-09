import CountingMatroid.Analysis.BoundedUniformSuccessWords

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-! Covered successful bounded draws are subuniform, including the zero-bit
singleton draw. The estimate sums all stopping cursors before composing a
fresh-suffix continuation. -/
namespace CountingMatroid.Analysis.BoundedUniformSubkernel
open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.FiniteStoppedFiberMass
open CountingMatroid.Analysis.BoundedUniformSuccessWords

/-- INTERNAL: Every event on a finite fair suffix has mass at most one. -/
theorem fair_mass_le_one (head : List Bool) (t : ℕ) (E : (ℕ → Bool) → Prop) :
    fairMass head t E ≤ 1 := by
  classical
  calc
    fairMass head t E ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro bits _
      split_ifs <;> first | exact le_rfl | positivity
    _ = 1 := by simp [card_vector]

/-- INTERNAL: Covered successes give equal mass to any two in-range values,
even when the suffix cuts off the last rejection word.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_value_symmetry (head : List Bool)
    (trials v t a b : ℕ) (hv : 2 ≤ v) (ha : a < v) (hb : b < v) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a, stop)) =
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some b, stop)) := by
  classical
  let draw := fun tape => (boundedUniform tape trials v head.length).val.1.map
    (fun value => (value, (boundedUniform tape trials v head.length).val.2))
  have hmap (tape : ℕ → Bool) (value stop : ℕ) :
      draw tape = some (value, stop) ↔
        (boundedUniform tape trials v head.length).val = (some value, stop) := by
    dsimp [draw]
    cases (boundedUniform tape trials v head.length).val with
    | mk choice cursor => cases choice <;> simp [Prod.mk.injEq]
  have hsplit (value : ℕ) := fairMass_stop_sum head t draw value (fun _ _ => True)
  simp only [and_true, hmap] at hsplit
  rw [hsplit a, hsplit b]
  apply Finset.sum_congr rfl
  intro stop _
  by_cases hform : ∃ k < trials,
      stop.val = head.length + (k + 1) * ((v - 1).log2 + 1)
  · obtain ⟨k, hk, hstop⟩ := hform
    have hc : (k + 1) * ((v - 1).log2 + 1) ≤ t := by omega
    rw [hstop, bounded_uniform_success_mass head trials v t k a hv hk ha hc,
      bounded_uniform_success_mass head trials v t k b hv hk hb hc]
  · have hz (value : ℕ) : fairMass head t (fun tape =>
        (boundedUniform tape trials v head.length).val = (some value, stop.val)) = 0 := by
      unfold fairMass
      apply Finset.sum_eq_zero
      intro bits _
      apply if_neg
      intro hrun
      obtain ⟨k, hk, hs, _⟩ :=
        (bounded_uniform_success_words _ trials v head.length value stop.val hv).mp hrun
      exact hform ⟨k, hk, hs⟩
    rw [hz a, hz b]

/-- INTERNAL: Summing over in-range values counts each successful draw at
most once; its capped successful law may have total mass below one. -/
theorem bounded_uniform_total_mass (head : List Bool) (trials v t : ℕ) :
    (∑ a : Fin v, fairMass head t (fun tape => ∃ stop,
      stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a.val, stop))) ≤ 1 := by
  classical
  unfold fairMass
  rw [Finset.sum_comm]
  calc
    _ ≤ ∑ _ : List.Vector Bool t, 1 / (2 : ℝ) ^ t := by
      apply Finset.sum_le_sum
      intro bits _
      let tape := finiteTape (head ++ bits.val)
      simp only
      by_cases he : ∃ a : Fin v, ∃ stop, stop ≤ head.length + t ∧
          (boundedUniform tape trials v head.length).val = (some a.val, stop)
      · obtain ⟨a, stop, hs, hrun⟩ := he
        rw [Finset.sum_eq_single a]
        · rw [if_pos ⟨stop, hs, hrun⟩]
        · intro b _ hba
          apply if_neg
          rintro ⟨stopB, _, hB⟩
          have hab : a.val = b.val := by
            have h := congrArg Prod.fst (hrun.symm.trans hB)
            exact Option.some.inj h
          exact hba (Fin.ext hab.symm)
        · simp
      · have hz : (∑ a : Fin v, if ∃ stop, stop ≤ head.length + t ∧
            (boundedUniform tape trials v head.length).val = (some a.val, stop)
            then 1 / (2 : ℝ) ^ t else 0) = 0 := by
          apply Finset.sum_eq_zero
          intro a _
          exact if_neg (fun h => he ⟨a, h⟩)
        calc
          _ = (∑ a : Fin v, if ∃ stop, stop ≤ head.length + t ∧
              (boundedUniform tape trials v head.length).val = (some a.val, stop)
              then 1 / (2 : ℝ) ^ t else 0) := by
            apply Finset.sum_congr rfl
            intro a _
            split_ifs <;> rfl
          _ = 0 := hz
          _ ≤ _ := by positivity
    _ = 1 := by simp [card_vector]

/-- INTERNAL: After summing all covered stopping endpoints, each successful
value has mass at most the corresponding exact uniform probability.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_covered_mass (head : List Bool)
    (trials v t value : ℕ) (hv : 0 < v) (ha : value < v) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some value, stop)) ≤
      1 / (v : ℝ) := by
  classical
  by_cases htwo : 2 ≤ v
  · have hsum := bounded_uniform_total_mass head trials v t
    have heq (a : Fin v) := bounded_uniform_value_symmetry head trials v t
      a.val value htwo a.isLt ha
    simp_rw [heq] at hsum
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    apply (le_div_iff₀ (by exact_mod_cast hv : (0 : ℝ) < v)).mpr
    simpa only [mul_comm] using hsum
  · have hvone : v = 1 := by omega
    subst v
    simpa using fair_mass_le_one head t (fun tape => ∃ stop,
      stop ≤ head.length + t ∧
      (boundedUniform tape trials 1 head.length).val = (some value, stop))

/-- INTERNAL: Covered capped draws followed by a uniformly bounded fresh
continuation cost at most 1/v times that continuation bound, summed over
all possible endpoints rather than at one fixed endpoint.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_stopped_continuation (head : List Bool)
    (trials v t value : ℕ) (hv : 0 < v) (ha : value < v)
    (E : (ℕ → Bool) → ℕ → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ stop, head.length ≤ stop → stop ≤ head.length + t →
      ∀ pref : List.Vector Bool (stop - head.length),
      (boundedUniform (finiteTape (head ++ pref.val)) trials v head.length).val =
        (some value, stop) →
      fairMass (head ++ pref.val) (t - (stop - head.length))
        (fun tape => E tape stop) ≤ B) :
    fairMass head t (fun tape => ∃ stop, stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some value, stop) ∧
      E tape stop) ≤ (1 / (v : ℝ)) * B := by
  let draw := fun tape => (boundedUniform tape trials v head.length).val.1.map
    (fun value => (value, (boundedUniform tape trials v head.length).val.2))
  have hmap (tape : ℕ → Bool) (a stop : ℕ) :
      draw tape = some (a, stop) ↔
        (boundedUniform tape trials v head.length).val = (some a, stop) := by
    dsimp [draw]
    cases (boundedUniform tape trials v head.length).val with
    | mk choice cursor => cases choice <;> simp [Prod.mk.injEq]
  have hbound := stopped_next_bound head t draw
    (bounded_uniform_success_interval trials v head.length) value E B hB (by
      intro stop hlo hhi pref hrun
      exact hcont stop hlo hhi pref ((hmap _ _ _).mp hrun))
  simp only [hmap] at hbound
  exact hbound.trans (mul_le_mul_of_nonneg_right
    (bounded_uniform_covered_mass head trials v t value hv ha) hB)

/-- INTERNAL: Finite unions have at most the sum of their event masses. -/
theorem fair_mass_exists_le_sum {α : Type} [Fintype α] (head : List Bool)
    (t : ℕ) (E : α → (ℕ → Bool) → Prop) :
    fairMass head t (fun tape => ∃ a, E a tape) ≤
      ∑ a : α, fairMass head t (E a) := by
  classical
  unfold fairMass
  rw [Finset.sum_comm]
  apply Finset.sum_le_sum
  intro bits _
  by_cases he : ∃ a, E a (finiteTape (head ++ bits.val))
  · obtain ⟨a, ha⟩ := he
    rw [if_pos ⟨a, ha⟩]
    calc
      _ = (if E a (finiteTape (head ++ bits.val)) then 1 / (2 : ℝ) ^ t else 0) :=
        (if_pos ha).symm
      _ ≤ _ := Finset.single_le_sum
        (f := fun b : α => if E b (finiteTape (head ++ bits.val))
          then 1 / (2 : ℝ) ^ t else 0)
        (fun b _ => by split_ifs <;> positivity) (Finset.mem_univ a)
  · rw [if_neg he]
    exact Finset.sum_nonneg (fun a _ => by split_ifs <;> positivity)

/-- INTERNAL: Compose an adaptive bounded integer draw with value-dependent
fresh continuations; aborts and uncovered endpoints contribute zero.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_bind_mass (head : List Bool) (trials v t : ℕ)
    (hv : 0 < v) (E : Fin v → (ℕ → Bool) → ℕ → Prop) (B : Fin v → ℝ)
    (hB : ∀ a, 0 ≤ B a)
    (hcont : ∀ (a : Fin v) (stop : ℕ), head.length ≤ stop → stop ≤ head.length + t →
      ∀ pref : List.Vector Bool (stop - head.length),
      (boundedUniform (finiteTape (head ++ pref.val)) trials v head.length).val =
        (some a.val, stop) →
      fairMass (head ++ pref.val) (t - (stop - head.length))
        (fun tape => E a tape stop) ≤ B a) :
    fairMass head t (fun tape => ∃ (a : Fin v) (stop : ℕ),
      stop ≤ head.length + t ∧
      (boundedUniform tape trials v head.length).val = (some a.val, stop) ∧
      E a tape stop) ≤ (1 / (v : ℝ)) * ∑ a : Fin v, B a := by
  calc
    _ ≤ ∑ a : Fin v, fairMass head t (fun tape => ∃ stop,
        stop ≤ head.length + t ∧
        (boundedUniform tape trials v head.length).val = (some a.val, stop) ∧
        E a tape stop) := fair_mass_exists_le_sum head t _
    _ ≤ ∑ a : Fin v, (1 / (v : ℝ)) * B a := Finset.sum_le_sum (fun a _ =>
      bounded_uniform_stopped_continuation head trials v t a.val hv a.isLt
        (E a) (B a) (hB a) (hcont a))
    _ = _ := (Finset.mul_sum _ _ _).symm

end CountingMatroid.Analysis.BoundedUniformSubkernel
