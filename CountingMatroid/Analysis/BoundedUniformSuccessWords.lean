import CountingMatroid.Analysis.BoundedUniformAbortMass
import CountingMatroid.Analysis.FiniteStoppedFiberMass
import Mathlib.Order.Interval.Finset.Fin

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

/-!
Successful capped integer draws are characterized by their first accepted
word. The characterization records both the returned integer and the consumed
cursor, with all earlier fixed-width words rejected. Binary-word enumeration
counts the corresponding finite fair-bit cylinders exactly. Interval replay
then transfers fresh-suffix continuation bounds at each successful endpoint.
-/

namespace CountingMatroid.Analysis.BoundedUniformSuccessWords

open CountingMatroid.Model CountingMatroid.Program
open CountingMatroid.Analysis.BoundedUniformAbortMass

/-- INTERNAL: The fixed-width word scan adds its initial accumulator times
its binary place value to the value of the newly read bits.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_accumulator (tape : ℕ → Bool) (width value start : ℕ) :
    (readWord tape width value start).1 =
      value * 2 ^ width + (readWord tape width 0 start).1 := by
  induction width generalizing value start with
  | zero => simp [readWord]
  | succ width ih =>
    simp only [readWord]
    rw [ih (2 * value + if tape start then 1 else 0) (start + 1),
      ih (2 * 0 + if tape start then 1 else 0) (start + 1), pow_succ]
    ring

/-- INTERNAL: Equal fixed-width binary values identify every bit in the
consumed word; conversely, equal word bits give equal values.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_value_eq_iff (tape other : ℕ → Bool) (width start : ℕ) :
    (readWord tape width 0 start).1 = (readWord other width 0 start).1 ↔
      ∀ i, start ≤ i → i < start + width → tape i = other i := by
  induction width generalizing start with
  | zero =>
    simp only [readWord, Nat.add_zero, true_iff]
    intro i hlo hhi
    omega
  | succ width ih =>
    have ht := readWord_lt tape width 0 (start + 1)
    have ho := readWord_lt other width 0 (start + 1)
    simp only [Nat.zero_add, Nat.one_mul] at ht ho
    have hvalue : (readWord tape (width + 1) 0 start).1 =
        (if tape start then 1 else 0) * 2 ^ width +
          (readWord tape width 0 (start + 1)).1 := by
      simpa only [readWord, Nat.mul_zero, Nat.zero_add] using
        read_word_accumulator tape width (if tape start then 1 else 0) (start + 1)
    have hother : (readWord other (width + 1) 0 start).1 =
        (if other start then 1 else 0) * 2 ^ width +
          (readWord other width 0 (start + 1)).1 := by
      simpa only [readWord, Nat.mul_zero, Nat.zero_add] using
        read_word_accumulator other width (if other start then 1 else 0) (start + 1)
    rw [hvalue, hother]
    constructor
    · intro h
      have hb : tape start = other start := by
        cases hb : tape start <;> cases hc : other start <;>
          simp only [hb, hc, Bool.false_eq_true, ite_false, ite_true,
            Nat.zero_mul, Nat.zero_add, Nat.one_mul] at h ⊢ <;> omega
      have htail : (readWord tape width 0 (start + 1)).1 =
          (readWord other width 0 (start + 1)).1 := by
        rw [hb] at h
        omega
      have hagree := (ih (start + 1)).mp htail
      intro i hlo hhi
      by_cases hi : i = start
      · subst i; exact hb
      · exact hagree i (by omega) (by omega)
    · intro h
      have hb := h start le_rfl (by omega)
      have htail := (ih (start + 1)).mpr (fun i hlo hhi =>
        h i (by omega) (by omega))
      rw [hb, htail]

/-- INTERNAL: Reading equal bit strings at possibly different cursor
positions gives equal binary values.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_eq_of_bits (tape other : ℕ → Bool) (width value start otherStart : ℕ)
    (h : ∀ i < width, tape (start + i) = other (otherStart + i)) :
    (readWord tape width value start).1 = (readWord other width value otherStart).1 := by
  induction width generalizing value start otherStart with
  | zero => rfl
  | succ width ih =>
    have hb := h 0 (by omega)
    simp only [Nat.add_zero] at hb
    simp only [readWord, hb]
    apply ih
    intro i hi
    simpa only [Nat.add_assoc, Nat.add_comm 1 i] using h (i + 1) (by omega)

/-- INTERNAL: All width-bit strings enumerate the integers below 2^width
exactly once, under the program's actual most-significant-bit-first scan.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_bijective (width : ℕ) :
    Function.Bijective (fun bits : List.Vector Bool width =>
      (⟨(readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1,
        by simpa only [Nat.zero_add, Nat.one_mul] using
          readWord_lt (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0⟩ :
          Fin (2 ^ width))) := by
  classical
  apply (Fintype.bijective_iff_injective_and_card _).mpr
  refine ⟨?_, by simp [card_vector]⟩
  intro a b heq
  have hv := congrArg Fin.val heq
  have hbits := (read_word_value_eq_iff
    (FiniteStoppedFiberMass.finiteTape a.val)
    (FiniteStoppedFiberMass.finiteTape b.val) width 0).mp hv
  apply List.Vector.ext
  intro i
  have h := hbits i.val (by omega) (by simpa using i.isLt)
  simpa [FiniteStoppedFiberMass.finiteTape, List.Vector.get,
    List.getElem?_eq_getElem, a.property, b.property, i.isLt] using h

/-- INTERNAL: A complete fresh word has the uniform sum over its binary
values, with no dependence on the preceding history.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_sum (width : ℕ) (F : ℕ → ℝ) :
    (∑ bits : List.Vector Bool width,
      F (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1) =
      ∑ value : Fin (2 ^ width), F value.val := by
  exact Fintype.sum_bijective _ (read_word_bijective width) _ _ (fun _ => rfl)

/-- INTERNAL: A fresh word's binary value is unchanged by extending either
its previously consumed head or its later suffix.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_after_prefix (head : List Bool) (width : ℕ)
    (bits : List.Vector Bool width) (tail : List Bool) :
    (readWord (FiniteStoppedFiberMass.finiteTape ((head ++ bits.val) ++ tail))
      width 0 head.length).1 =
      (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 := by
  apply read_word_eq_of_bits
  intro i hi
  unfold FiniteStoppedFiberMass.finiteTape
  rw [List.append_assoc, List.getElem?_append_right (by omega),
    Nat.add_sub_cancel_left, List.getElem?_append_left (by simpa only [bits.property] using hi)]
  simp only [Nat.zero_add]

/-- INTERNAL: Count the rejected integers in a complete binary word.
TEXLINE: main.tex:1392-1401 -/
theorem read_word_rejected_sum (width v : ℕ) (hv : v ≤ 2 ^ width) :
    (∑ bits : List.Vector Bool width,
      if v ≤ (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1
      then (1 : ℝ) else 0) = ((2 ^ width - v : ℕ) : ℝ) := by
  classical
  rw [read_word_sum width (fun x => if v ≤ x then (1 : ℝ) else 0)]
  by_cases hlt : v < 2 ^ width
  · let a : Fin (2 ^ width) := ⟨v, hlt⟩
    have hf : (Finset.univ.filter (fun value : Fin (2 ^ width) => v ≤ value.val)) =
        Finset.Ici a := by
      ext value
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_Ici]
      rfl
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, hf, Fin.card_Ici]
  · have heq : v = 2 ^ width := by omega
    subst v
    simp only [Nat.sub_self, Nat.cast_zero]
    apply Finset.sum_eq_zero
    intro value _
    exact if_neg (by omega)

/-- INTERNAL: The first accepted word after k rejections has its exact
finite fair-suffix mass. No output uniformity is assumed in the proof.
TEXLINE: main.tex:1392-1401 -/
theorem first_accepted_word_mass (head : List Bool) (t width v k value : ℕ)
    (hw : 0 < width) (hv : v ≤ 2 ^ width) (ha : value < v)
    (hcover : (k + 1) * width ≤ t) :
    FiniteStoppedFiberMass.fairMass head t (fun tape =>
      (readWord tape width 0 (head.length + k * width)).1 = value ∧
      ∀ j < k, v ≤ (readWord tape width 0 (head.length + j * width)).1) =
      ((2 ^ width - v : ℕ) : ℝ) ^ k / (2 : ℝ) ^ ((k + 1) * width) := by
  classical
  induction k generalizing head t with
  | zero =>
    simp only [Nat.zero_mul, Nat.add_zero, Nat.zero_add, Nat.one_mul, pow_zero]
    rw [FiniteStoppedFiberMass.fairMass_split head t width (by omega)]
    have hconst (bits : List.Vector Bool width) :
        FiniteStoppedFiberMass.fairMass (head ++ bits.val) (t - width)
          (fun tape => (readWord tape width 0 head.length).1 = value ∧
            ∀ j < 0, v ≤ (readWord tape width 0 (head.length + j * width)).1) =
          if (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 = value
          then 1 else 0 := by
      unfold FiniteStoppedFiberMass.fairMass
      simp_rw [read_word_after_prefix head width bits]
      simp only [Nat.not_lt_zero, IsEmpty.forall_iff, forall_const, and_true]
      split_ifs <;> simp [card_vector]
    simp_rw [hconst, mul_ite, mul_one, mul_zero]
    rw [read_word_sum width (fun x => if x = value then 1 / (2 : ℝ) ^ width else 0)]
    let a : Fin (2 ^ width) := ⟨value, lt_of_lt_of_le ha hv⟩
    have heq (i : Fin (2 ^ width)) : i.val = value ↔ i = a := by
      exact ⟨fun h => Fin.ext h, fun h => congrArg Fin.val h⟩
    simp_rw [heq]
    simp
  | succ k ih =>
    rw [FiniteStoppedFiberMass.fairMass_split head t width (by nlinarith)]
    have hpart (bits : List.Vector Bool width) :
        FiniteStoppedFiberMass.fairMass (head ++ bits.val) (t - width)
          (fun tape => (readWord tape width 0 (head.length + (k + 1) * width)).1 = value ∧
            ∀ j < k + 1, v ≤ (readWord tape width 0 (head.length + j * width)).1) =
        (if v ≤ (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1
          then (1 : ℝ) else 0) *
        FiniteStoppedFiberMass.fairMass (head ++ bits.val) (t - width)
          (fun tape => (readWord tape width 0 ((head ++ bits.val).length + k * width)).1 = value ∧
            ∀ j < k, v ≤ (readWord tape width 0 ((head ++ bits.val).length + j * width)).1) := by
      unfold FiniteStoppedFiberMass.fairMass
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro tail _
      let tape := FiniteStoppedFiberMass.finiteTape ((head ++ bits.val) ++ tail.val)
      have hlen : (head ++ bits.val).length = head.length + width := by simp
      have hhead : (readWord tape width 0 head.length).1 =
          (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 :=
        read_word_after_prefix head width bits tail.val
      have hoff (j : ℕ) : head.length + (j + 1) * width =
          (head ++ bits.val).length + j * width := by rw [hlen]; ring
      have hevent : ((readWord tape width 0 (head.length + (k + 1) * width)).1 = value ∧
          ∀ j < k + 1, v ≤ (readWord tape width 0 (head.length + j * width)).1) ↔
          v ≤ (readWord (FiniteStoppedFiberMass.finiteTape bits.val) width 0 0).1 ∧
          ((readWord tape width 0 ((head ++ bits.val).length + k * width)).1 = value ∧
          ∀ j < k, v ≤ (readWord tape width 0 ((head ++ bits.val).length + j * width)).1) := by
        rw [hoff k]
        constructor
        · rintro ⟨hval, hall⟩
          refine ⟨?_, hval, ?_⟩
          · simpa only [Nat.zero_mul, Nat.add_zero, hhead] using hall 0 (by omega)
          · intro j hj
            simpa only [hoff j] using hall (j + 1) (by omega)
        · rintro ⟨hfirst, hval, hall⟩
          refine ⟨hval, ?_⟩
          intro j hj
          cases j with
          | zero => simpa only [Nat.zero_mul, Nat.add_zero, hhead] using hfirst
          | succ j => simpa only [hoff j] using hall j (by omega)
      dsimp only [tape] at hevent
      simp +instances only [hevent, ite_and, ite_mul, one_mul, zero_mul]
      split_ifs <;> simp_all
      exfalso
      rename_i hfirst hvalue hbad hall
      obtain ⟨j, hj, hlt⟩ := hbad
      have hle := hall j hj
      omega
    have htailcover : (k + 1) * width ≤ t - width := by
      have hc : (k + 1) * width + width ≤ t := by nlinarith [hcover]
      omega
    simp_rw [hpart, ih (head ++ _) (t - width) htailcover]
    have hsum := read_word_rejected_sum width v hv
    have hfactor (x : ℝ) : (1 / (2 : ℝ) ^ width) *
        (x * (((2 ^ width - v : ℕ) : ℝ) ^ k / (2 : ℝ) ^ ((k + 1) * width))) =
        x * (((2 ^ width - v : ℕ) : ℝ) ^ k /
          ((2 : ℝ) ^ width * (2 : ℝ) ^ ((k + 1) * width))) := by ring
    simp_rw [hfactor]
    rw [← Finset.sum_mul, hsum]
    rw [← pow_add, show width + (k + 1) * width = (k + 1 + 1) * width by ring,
      pow_succ]
    ring

/-- INTERNAL: Exact first-accepted-word characterization of the absorbing
trial loop, including its stopping cursor.
TEXLINE: main.tex:1392-1401 -/
theorem sample_words_success_iff (tape : ℕ → Bool)
    (v trials start value stop : ℕ) :
    sampleWords tape v trials (none, start) = (some value, stop) ↔
      ∃ k < trials,
        stop = start + (k + 1) * ((v - 1).log2 + 1) ∧
        value < v ∧
        (readWord tape ((v - 1).log2 + 1) 0
          (start + k * ((v - 1).log2 + 1))).1 = value ∧
        ∀ j < k, v ≤ (readWord tape ((v - 1).log2 + 1) 0
          (start + j * ((v - 1).log2 + 1))).1 := by
  let width := (v - 1).log2 + 1
  change sampleWords tape v trials (none, start) = (some value, stop) ↔
    ∃ k < trials, stop = start + (k + 1) * width ∧ value < v ∧
      (readWord tape width 0 (start + k * width)).1 = value ∧
      ∀ j < k, v ≤ (readWord tape width 0 (start + j * width)).1
  induction trials generalizing start with
  | zero => simp [sampleWords]
  | succ trials ih =>
    simp only [sampleWords, Option.isSome_none, Bool.false_eq_true, ite_false]
    by_cases ha : (readWord tape width 0 start).1 < v
    · rw [if_pos ha, sampleWords_some]
      constructor
      · intro h
        have hvalue := congrArg (fun p : Option ℕ × ℕ => p.1) h
        have hstop := congrArg (fun p : Option ℕ × ℕ => p.2) h
        have hv : (readWord tape width 0 start).1 = value := Option.some.inj hvalue
        refine ⟨0, by omega, ?_, ?_, ?_, ?_⟩
        · simpa only [Nat.zero_add, Nat.one_mul, readWord_cursor] using hstop.symm
        · simpa only [hv] using ha
        · simpa only [Nat.zero_mul, Nat.add_zero] using hv
        · intro j hj; omega
      · rintro ⟨k, hk, hc, hv, hword, hrejected⟩
        have hk0 : k = 0 := by
          by_contra hn
          have hr := hrejected 0 (by omega)
          simp only [Nat.zero_mul, Nat.add_zero] at hr
          omega
        subst k
        simp only [Nat.zero_mul, Nat.add_zero] at hword
        rw [readWord_cursor]
        simp only [Nat.zero_add, Nat.one_mul] at hc
        exact Prod.ext (congrArg some hword) hc.symm
    · rw [if_neg ha, readWord_cursor, ih]
      constructor
      · rintro ⟨k, hk, hc, hv, hword, hrejected⟩
        refine ⟨k + 1, by omega, ?_, hv, ?_, ?_⟩
        · calc
            stop = start + width + (k + 1) * width := hc
            _ = start + (k + 1 + 1) * width := by ring
        · convert hword using 1
          congr 2
          simp only [width]
          ring
        · intro j hj
          cases j with
          | zero => simpa only [Nat.zero_mul, Nat.add_zero] using Nat.le_of_not_gt ha
          | succ j =>
            have hr := hrejected j (by omega)
            convert hr using 1
            congr 2
            simp only [width]
            ring
      · rintro ⟨k, hk, hc, hv, hword, hrejected⟩
        have hkpos : 0 < k := by
          by_contra hn
          have hk0 : k = 0 := by omega
          subst k
          simp only [Nat.zero_mul, Nat.add_zero] at hword
          exact ha (hword ▸ hv)
        obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hkpos)
        refine ⟨j, by omega, ?_, hv, ?_, ?_⟩
        · calc
            stop = start + (j + 1 + 1) * width := hc
            _ = start + width + (j + 1) * width := by ring
        · convert hword using 1
          congr 2
          simp only [width, Nat.succ_eq_add_one]
          ring
        · intro i hi
          have hr := hrejected (i + 1) (by omega)
          convert hr using 1
          congr 2
          simp only [width]
          ring

/-- INTERNAL: A successful nonsingleton bounded draw has exactly k rejected
words followed by its returned value, and stops at that word's boundary.
TEXLINE: main.tex:1392-1401 -/
theorem bounded_uniform_success_words (tape : ℕ → Bool)
    (trials v start value stop : ℕ) (hv : 2 ≤ v) :
    (boundedUniform tape trials v start).val = (some value, stop) ↔
      ∃ k < trials,
        stop = start + (k + 1) * ((v - 1).log2 + 1) ∧
        value < v ∧
        (readWord tape ((v - 1).log2 + 1) 0
          (start + k * ((v - 1).log2 + 1))).1 = value ∧
        ∀ j < k, v ≤ (readWord tape ((v - 1).log2 + 1) 0
          (start + j * ((v - 1).log2 + 1))).1 := by
  rw [boundedUniform_value tape trials v start hv]
  exact sample_words_success_iff tape v trials start value stop

/-- INTERNAL: Joint value/cursor law for a successful capped integer draw.
Its k earlier rejection words contribute their exact cylinder count; the
unused suffix is unrestricted. This is an unnormalised successful mass.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_success_mass (head : List Bool)
    (trials v t k value : ℕ) (hv : 2 ≤ v) (hk : k < trials) (ha : value < v)
    (hcover : (k + 1) * ((v - 1).log2 + 1) ≤ t) :
    FiniteStoppedFiberMass.fairMass head t (fun tape =>
      (boundedUniform tape trials v head.length).val =
        (some value, head.length + (k + 1) * ((v - 1).log2 + 1))) =
      ((2 ^ ((v - 1).log2 + 1) - v : ℕ) : ℝ) ^ k /
        (2 : ℝ) ^ ((k + 1) * ((v - 1).log2 + 1)) := by
  let width := (v - 1).log2 + 1
  have hw : 0 < width := by dsimp [width]; omega
  have hvword : v ≤ 2 ^ width := by
    have hb := Nat.lt_log2_self (n := v - 1)
    dsimp only [width]
    omega
  have hevent (tape : ℕ → Bool) :
      (boundedUniform tape trials v head.length).val =
          (some value, head.length + (k + 1) * width) ↔
      (readWord tape width 0 (head.length + k * width)).1 = value ∧
        ∀ j < k, v ≤ (readWord tape width 0 (head.length + j * width)).1 := by
    rw [bounded_uniform_success_words tape trials v head.length value _ hv]
    constructor
    · rintro ⟨j, _, hstop, _, hword, hrejected⟩
      have hj : j = k := by
        change head.length + (k + 1) * width = head.length + (j + 1) * width at hstop
        nlinarith
      subst j
      exact ⟨hword, hrejected⟩
    · rintro ⟨hword, hrejected⟩
      exact ⟨k, hk, rfl, ha, hword, hrejected⟩
  have hfun : (fun tape => (boundedUniform tape trials v head.length).val =
      (some value, head.length + (k + 1) * width)) =
      (fun tape => (readWord tape width 0 (head.length + k * width)).1 = value ∧
        ∀ j < k, v ≤ (readWord tape width 0 (head.length + j * width)).1) :=
    funext (fun tape => propext (hevent tape))
  change FiniteStoppedFiberMass.fairMass head t
    (fun tape => (boundedUniform tape trials v head.length).val =
      (some value, head.length + (k + 1) * width)) = _
  rw [hfun]
  exact first_accepted_word_mass head t width v k value hw hvword ha hcover

/-- INTERNAL: Converting the sampler's optional value and retained cursor
into an optional pair preserves every successful value/cursor equality. -/
private theorem uniform_pair_map_eq (draw : Option ℕ × ℕ) (value stop : ℕ) :
    draw.1.map (fun a => (a, draw.2)) = some (value, stop) ↔
      draw = (some value, stop) := by
  rcases draw with ⟨choice, cursor⟩
  cases choice <;> simp [Prod.mk.injEq]

/-- INTERNAL: Successful integer draws replay on their consumed interval
when the retained cursor is packaged with the optional successful value.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_success_interval (trials v start : ℕ) :
    ChainStepIntervalReplay.SuccessReplay (fun tape =>
      (boundedUniform tape trials v start).val.1.map
        (fun a => (a, (boundedUniform tape trials v start).val.2)))
      Prod.snd start := by
  intro tape out hrun
  have hp := (uniform_pair_map_eq _ out.1 out.2).mp hrun
  have hr := BoundedUniformReplay.boundedUniform_interval_replay trials v start tape
  refine ⟨?_, ?_⟩
  · simpa only [hp] using hr.1
  · intro other hagree
    apply (uniform_pair_map_eq _ out.1 out.2).mpr
    exact (hr.2 other (by simpa only [hp] using hagree)).trans hp

/-- INTERNAL: A uniform fresh-suffix continuation estimate multiplies the
exact successful integer value/cursor mass, without discarding aborts.
TEXLINE: main.tex:1392-1401,1415-1421 -/
theorem bounded_uniform_continuation_mass (head : List Bool)
    (trials v t k value : ℕ) (hv : 2 ≤ v) (hk : k < trials) (ha : value < v)
    (hcover : (k + 1) * ((v - 1).log2 + 1) ≤ t)
    (E : (ℕ → Bool) → Prop) (B : ℝ) (hB : 0 ≤ B)
    (hcont : ∀ pref : List.Vector Bool ((k + 1) * ((v - 1).log2 + 1)),
      (boundedUniform (FiniteStoppedFiberMass.finiteTape (head ++ pref.val))
        trials v head.length).val =
        (some value, head.length + (k + 1) * ((v - 1).log2 + 1)) →
      FiniteStoppedFiberMass.fairMass (head ++ pref.val)
        (t - (k + 1) * ((v - 1).log2 + 1)) E ≤ B) :
    FiniteStoppedFiberMass.fairMass head t (fun tape =>
      (boundedUniform tape trials v head.length).val =
        (some value, head.length + (k + 1) * ((v - 1).log2 + 1)) ∧ E tape) ≤
      (((2 ^ ((v - 1).log2 + 1) - v : ℕ) : ℝ) ^ k /
        (2 : ℝ) ^ ((k + 1) * ((v - 1).log2 + 1))) * B := by
  let stop := head.length + (k + 1) * ((v - 1).log2 + 1)
  let f := fun tape => (boundedUniform tape trials v head.length).val.1.map
    (fun a => (a, (boundedUniform tape trials v head.length).val.2))
  have hbound := FiniteStoppedFiberMass.stopped_fiber_bound head t f Prod.snd
    (bounded_uniform_success_interval trials v head.length) (value, stop)
    (by dsimp [stop]; omega) (by dsimp [stop]; omega) E B hB (by
      intro pref hrun
      let pref' : List.Vector Bool ((k + 1) * ((v - 1).log2 + 1)) :=
        ⟨pref.val, by simpa only [stop, Prod.snd, Nat.add_sub_cancel_left] using pref.property⟩
      have hp := (uniform_pair_map_eq _ value stop).mp hrun
      simpa only [stop, Prod.snd, Nat.add_sub_cancel_left] using hcont pref' hp)
  dsimp only [f] at hbound
  simp_rw [uniform_pair_map_eq] at hbound
  dsimp only [stop] at hbound
  rw [bounded_uniform_success_mass head trials v t k value hv hk ha hcover] at hbound
  exact hbound

end CountingMatroid.Analysis.BoundedUniformSuccessWords

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · binary-word injectivity and finite-cardinality enumeration give the exact first-accepted-word cylinder mass. The sampler normal form identifies its stopping word uniquely, yielding the joint value/cursor law; successful interval replay and stopped_fiber_bound transfer a fresh-suffix continuation estimate. All declarations are proved.
-/
