import Mathlib.Data.Set.Finite.List
import Mathlib.Data.Set.Card.Arithmetic
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Data.List.Infix
import Mathlib.Data.ENNReal.Inv

set_option autoImplicit false

/-!
Finite fair-bit conditioning by a consumed prefix. Appending a fixed prefix
is a bijection on its suffix event; disjoint consumed-prefix cylinders let
uniform suffix estimates transfer to the whole finite tape. This module
proves only counting facts, not the program's stopping-prefix property or
the phase's conditional analytic estimate.
-/

namespace CountingMatroid.Analysis.FiniteTapePrefixBound

/-- INTERNAL: There are exactly `2^m` Boolean tapes of length `m`.
TEXLINE: main.tex:1392-1421 -/
theorem fair_lists_ncard (m : ℕ) :
    Set.ncard {bits : List Bool | bits.length = m} = 2 ^ m := by
  change Nat.card (List.Vector Bool m) = _
  rw [Nat.card_eq_fintype_card, card_vector]
  simp

/-- INTERNAL: Deleting a fixed consumed prefix bijects its tape event with
an event on all remaining suffixes. No condition on the suffix event is needed.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem append_event_ncard (m : ℕ) (pref : List Bool)
    (hlen : pref.length ≤ m) (E : List Bool → Prop) :
    Set.ncard {bits : List Bool | bits.length = m ∧ pref <+: bits ∧ E bits} =
      Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} := by
  rw [← Set.ncard_image_of_injective
    {suffix : List Bool | suffix.length = m - pref.length ∧ E (pref ++ suffix)}
    (List.append_right_injective pref)]
  congr 1
  ext bits
  constructor
  · rintro ⟨hb, hp, he⟩
    refine ⟨bits.drop pref.length, ⟨?_, ?_⟩, ?_⟩
    · simp only [List.length_drop, hb]
    · simpa only [← List.prefix_append_drop hp] using he
    · exact (List.prefix_append_drop hp).symm
  · rintro ⟨suffix, ⟨hs, he⟩, rfl⟩
    refine ⟨?_, List.prefix_append pref suffix, he⟩
    simp only [List.length_append, hs, Nat.add_sub_of_le hlen]

/-- INTERNAL: A fixed-prefix event has prefix mass times its fresh-suffix
mass under the finite uniform fair-bit law. This is the conditional-law
identity used before applying a uniform estimate for each successful history.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem append_event_mass (m : ℕ) (pref : List Bool)
    (hlen : pref.length ≤ m) (E : List Bool → Prop) :
    (Set.ncard {bits : List Bool | bits.length = m ∧ pref <+: bits ∧ E bits} :
      ENNReal) * (1 / 2 : ENNReal) ^ m =
    (1 / 2 : ENNReal) ^ pref.length *
      ((Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length)) := by
  rw [append_event_ncard m pref hlen E]
  have hp : (1 / 2 : ENNReal) ^ m =
      (1 / 2 : ENNReal) ^ pref.length * (1 / 2 : ENNReal) ^ (m - pref.length) := by
    rw [← Nat.add_sub_of_le hlen, pow_add]
    simp only [Nat.add_sub_cancel_left]
  rw [hp]
  ac_rfl

/-- INTERNAL: Successful stopping histories have prefix-free consumed
prefixes. A cursor beyond the finite block contributes the whole tape, so
this structural fact does not itself require a cursor-coverage bound.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem stopping_prefixes_free (m : ℕ) (S : Finset (List Bool))
    (cursor : List Bool → ℕ) (hlen : ∀ bits ∈ S, bits.length = m)
    (hreplay : ∀ bitsA ∈ S, ∀ bitsB ∈ S, cursor bitsA ≤ m →
      bitsA.take (cursor bitsA) <+: bitsB → cursor bitsB = cursor bitsA) :
    ∀ a ∈ S.image (fun bits => bits.take (cursor bits)),
      ∀ b ∈ S.image (fun bits => bits.take (cursor bits)), a <+: b → a = b := by
  intro a ha b hb hab
  obtain ⟨bitsA, hmA, rfl⟩ := Finset.mem_image.mp ha
  obtain ⟨bitsB, hmB, rfl⟩ := Finset.mem_image.mp hb
  apply hab.eq_of_length
  by_cases hwithin : cursor bitsA ≤ m
  · have hc := hreplay bitsA hmA bitsB hmB hwithin
      (hab.trans (List.take_prefix _ _))
    simp only [List.length_take, hlen bitsA hmA, hlen bitsB hmB, hc]
  · have hle := hab.length_le
    simp only [List.length_take, hlen bitsA hmA, hlen bitsB hmB] at hle ⊢
    omega

/-- INTERNAL: Prefix-free consumed histories define disjoint tape cylinders.
TEXLINE: main.tex:1207-1212 -/
theorem prefix_cylinder_disjoint (m : ℕ) (P : Finset (List Bool))
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b) :
    (P : Set (List Bool)).PairwiseDisjoint
      (fun pref => {bits : List Bool | bits.length = m ∧ pref <+: bits}) := by
  intro a ha b hb hab
  apply Set.disjoint_left.mpr
  intro bits hba hbb
  rcases List.prefix_or_prefix_of_prefix hba.2 hbb.2 with h | h
  · exact hab (hfree a ha b hb h)
  · exact hab (hfree b hb a ha h).symm

/-- INTERNAL: Prefix-free histories consume total fair-bit mass at most one,
even when their consumed lengths differ.
TEXLINE: main.tex:1207-1212,1392-1421 -/
theorem prefix_mass_le_one (m : ℕ) (P : Finset (List Bool))
    (hlen : ∀ pref ∈ P, pref.length ≤ m)
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b) :
    ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length ≤ 1 := by
  classical
  let cylinder := fun pref => {bits : List Bool | bits.length = m ∧ pref <+: bits}
  have hfinite (pref : List Bool) : (cylinder pref).Finite :=
    (List.finite_length_eq Bool m).subset (fun _ hb => hb.1)
  have hcard : (⋃ pref ∈ P, cylinder pref).ncard =
      ∑ pref ∈ P, (cylinder pref).ncard := by
    have hc := P.finite_toSet.ncard_biUnion (fun pref _ => hfinite pref)
      (prefix_cylinder_disjoint m P hfree)
    calc
      _ = ∑ᶠ pref ∈ (P : Set (List Bool)), (cylinder pref).ncard := hc
      _ = _ := finsum_mem_coe_finset (fun pref => (cylinder pref).ncard) P
  have hbound : (⋃ pref ∈ P, cylinder pref).ncard ≤ 2 ^ m := by
    rw [← fair_lists_ncard m]
    apply Set.ncard_le_ncard _ (List.finite_length_eq Bool m)
    intro bits hb
    obtain ⟨pref, hb⟩ := Set.mem_iUnion.mp hb
    obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
    exact hb.1
  have htwo : (2 : ENNReal) * (1 / 2) = 1 := by
    rw [div_eq_mul_inv, one_mul]
    exact ENNReal.mul_inv_cancel (by norm_num) (by simp)
  have hmass (pref : List Bool) (hp : pref ∈ P) :
      ((cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m =
        (1 / 2 : ENNReal) ^ pref.length := by
    have hc := append_event_mass m pref (hlen pref hp) (fun _ => True)
    simp only [and_true, fair_lists_ncard, Nat.cast_pow, Nat.cast_ofNat] at hc
    change ((cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m = _ at hc
    rw [← mul_pow, htwo,
      one_pow, mul_one] at hc
    exact hc
  calc
    ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length =
        ∑ pref ∈ P, ((cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
      apply Finset.sum_congr rfl
      intro pref hp
      exact (hmass pref hp).symm
    _ = ((⋃ pref ∈ P, cylinder pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
      rw [hcard, Nat.cast_sum, Finset.sum_mul]
    _ ≤ ((2 ^ m : ℕ) : ENNReal) * (1 / 2 : ENNReal) ^ m := by gcongr
    _ = 1 := by
      rw [Nat.cast_pow, Nat.cast_ofNat, ← mul_pow]
      rw [htwo, one_pow]

/-- INTERNAL: Uniform conditional failure bounds on the fresh suffixes after
prefix-free consumed histories imply the same unconditional tape bound.
Prefixes may have different lengths; no independence between phase events is
assumed. Coverage and prefix-freeness must be proved for the actual program.
TEXLINE: main.tex:1207-1212,1277-1285,1392-1427 -/
theorem finite_prefix_failure_bound (m : ℕ) (P : Finset (List Bool))
    (E : List Bool → Prop) (β : ENNReal)
    (hlen : ∀ pref ∈ P, pref.length ≤ m)
    (hfree : ∀ a ∈ P, ∀ b ∈ P, a <+: b → a = b)
    (hcover : ∀ bits, bits.length = m → E bits →
      ∃ pref ∈ P, pref <+: bits)
    (hconditional : ∀ pref ∈ P,
      (Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
        E (pref ++ suffix)} : ENNReal) *
        (1 / 2 : ENNReal) ^ (m - pref.length) ≤ β) :
    (Set.ncard {bits : List Bool | bits.length = m ∧ E bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ m ≤ β := by
  classical
  let part := fun pref => {bits : List Bool |
    bits.length = m ∧ pref <+: bits ∧ E bits}
  have hfinite : (⋃ pref ∈ P, part pref).Finite :=
    (List.finite_length_eq Bool m).subset (by
      intro bits hb
      obtain ⟨pref, hb⟩ := Set.mem_iUnion.mp hb
      obtain ⟨_, hb⟩ := Set.mem_iUnion.mp hb
      exact hb.1)
  have hcard : Set.ncard {bits : List Bool | bits.length = m ∧ E bits} ≤
      ∑ pref ∈ P, (part pref).ncard := by
    apply (Set.ncard_le_ncard _ hfinite).trans (P.set_ncard_biUnion_le part)
    intro bits hb
    obtain ⟨pref, hp, hprefix⟩ := hcover bits hb.1 hb.2
    exact Set.mem_iUnion.mpr ⟨pref, Set.mem_iUnion.mpr ⟨hp, hb.1, hprefix, hb.2⟩⟩
  calc
    (Set.ncard {bits : List Bool | bits.length = m ∧ E bits} : ENNReal) *
        (1 / 2 : ENNReal) ^ m ≤
      ((∑ pref ∈ P, (part pref).ncard : ℕ) : ENNReal) *
        (1 / 2 : ENNReal) ^ m := by gcongr
    _ = ∑ pref ∈ P, ((part pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m := by
      rw [Nat.cast_sum, Finset.sum_mul]
    _ ≤ ∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length * β := by
      apply Finset.sum_le_sum
      intro pref hp
      rw [show ((part pref).ncard : ENNReal) * (1 / 2 : ENNReal) ^ m =
        (1 / 2 : ENNReal) ^ pref.length *
          ((Set.ncard {suffix : List Bool | suffix.length = m - pref.length ∧
            E (pref ++ suffix)} : ENNReal) *
            (1 / 2 : ENNReal) ^ (m - pref.length)) from
              append_event_mass m pref (hlen pref hp) E]
      exact mul_le_mul_right (hconditional pref hp) _
    _ = (∑ pref ∈ P, (1 / 2 : ENNReal) ^ pref.length) * β :=
      (Finset.sum_mul ..).symm
    _ ≤ 1 * β := mul_le_mul_left (prefix_mass_le_one m P hlen hfree) β
    _ = β := one_mul β

end CountingMatroid.Analysis.FiniteTapePrefixBound

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · Boolean tape count, fixed-prefix event bijection and mass, stopping-prefix freeness, prefix-cylinder disjointness, total prefix mass bound, and transfer of uniform suffix bounds. These counting results are used by `FiniteTapeLowerTail`; actual successful-history replay and analytic phase bounds are separate obligations.
-/
