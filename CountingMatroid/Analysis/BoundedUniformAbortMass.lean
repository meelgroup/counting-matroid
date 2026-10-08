import CountingMatroid.Analysis.InitialRestartLaw
import CountingMatroid.Analysis.FiniteObservationMarkov

set_option autoImplicit false

/-!
Finite-bit rejection-cap bounds for the actual charged integer sampler.
A rejected trial has a true leading bit: a false leading bit produces an
integer below the positive denominator. Distinct trials use disjoint words.
Coverage is an explicit premise here; obtaining it for adaptive calls in a
whole phase restart remains an obligation of the consuming analysis.
-/

namespace CountingMatroid.Analysis.BoundedUniformAbortMass

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Value semantics of the sampler's inner fixed-width bit scan.
TEXLINE: main.tex:1392-1401 -/
def readWord (tape : ℕ → Bool) : ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, value, cursor => (value, cursor)
  | k + 1, value, cursor =>
      readWord tape k (2 * value + if tape cursor then 1 else 0) (cursor + 1)

/-- INTERNAL: The word scan consumes exactly its fixed width. -/
theorem readWord_cursor (tape : ℕ → Bool) (k value cursor : ℕ) :
    (readWord tape k value cursor).2 = cursor + k := by
  induction k generalizing value cursor with
  | zero => rfl
  | succ k ih => simp only [readWord, ih]; omega

/-- INTERNAL: Appending k Boolean digits stays below the next binary boundary. -/
theorem readWord_lt (tape : ℕ → Bool) (k value cursor : ℕ) :
    (readWord tape k value cursor).1 < (value + 1) * 2 ^ k := by
  induction k generalizing value cursor with
  | zero => simp [readWord]
  | succ k ih =>
      simp only [readWord]
      have h := ih (2 * value + if tape cursor then 1 else 0) (cursor + 1)
      rw [pow_succ]
      have hb : (if tape cursor then 1 else 0 : ℕ) ≤ 1 := by split <;> omega
      nlinarith [(by positivity : 0 < 2 ^ k)]

/-- INTERNAL: The charged inner loop is the binary scan above, rather than
an alternative random source. -/
theorem readWord_charged (tape : ℕ → Bool) (k value cursor : ℕ) :
    (Arlib.Computation.Charged.repeatFor (fun _ (inner : ℕ × ℕ) => do
      let bit ← fairBit tape inner.2
      let value ← appendBit inner.1 bit
      let next ← successor inner.2
      pure (value, next)) k (value, cursor)).val =
      readWord tape k value cursor := by
  have hfold (xs : List ℕ) (value cursor : ℕ) :
      (Arlib.Computation.Charged.foldl (fun inner _ => do
        let bit ← fairBit tape inner.2
        let value ← appendBit inner.1 bit
        let next ← successor inner.2
        pure (value, next)) xs (value, cursor)).val =
        readWord tape xs.length value cursor := by
    induction xs generalizing value cursor with
    | nil => rfl
    | cons x xs ih =>
        rw [Arlib.Computation.Charged.val_foldl_cons]
        simp only [Arlib.Computation.Charged.val_bind, fairBit, appendBit, successor,
          Arlib.Computation.Charged.val_op, Arlib.Computation.Charged.val_pure,
          List.length_cons, readWord]
        exact ih (2 * value + if tape cursor then 1 else 0) (cursor + 1)
  simpa only [Arlib.Computation.Charged.repeatFor, List.length_range] using
    hfold (List.range k) value cursor

/-- INTERNAL: A false leading bit makes a rejection word strictly less than
its positive nonsingleton denominator.
TEXLINE: main.tex:1394-1401 -/
theorem false_leading_bit_accepts (tape : ℕ → Bool) (v cursor : ℕ)
    (hv : 2 ≤ v) (hbit : tape cursor = false) :
    (readWord tape ((v - 1).log2 + 1) 0 cursor).1 < v := by
  simp only [readWord, hbit, Bool.false_eq_true, ite_false, mul_zero, zero_add]
  have h := readWord_lt tape (v - 1).log2 0 (cursor + 1)
  simp only [zero_add, one_mul] at h
  have hpow : 2 ^ (v - 1).log2 ≤ v - 1 := Nat.log2_self_le (by omega)
  omega

/-- INTERNAL: Value semantics of the absorbing rejection-trial loop.
TEXLINE: main.tex:1392-1401 -/
def sampleWords (tape : ℕ → Bool) (v : ℕ) : ℕ → Option ℕ × ℕ → Option ℕ × ℕ
  | 0, acc => acc
  | k + 1, acc =>
      sampleWords tape v k (if acc.1.isSome then acc else
        let word := readWord tape ((v - 1).log2 + 1) 0 acc.2
        if word.1 < v then (some word.1, word.2) else (none, word.2))

/-- INTERNAL: Once a rejection draw accepts, later trials leave it unchanged. -/
theorem sampleWords_some (tape : ℕ → Bool) (v k value cursor : ℕ) :
    sampleWords tape v k (some value, cursor) = (some value, cursor) := by
  induction k with
  | zero => rfl
  | succ k ih => simpa only [sampleWords, Option.isSome_some, ite_true] using ih

/-- INTERNAL: For a nonsingleton positive denominator, the charged sampler
is exactly the binary-word rejection loop.
TEXLINE: main.tex:1392-1401 -/
theorem boundedUniform_value (tape : ℕ → Bool) (trials v cursor : ℕ)
    (hv : 2 ≤ v) :
    (boundedUniform tape trials v cursor).val =
      sampleWords tape v trials (none, cursor) := by
  with_unfolding_all
    let step : Option ℕ × ℕ → Arlib.Computation.Charged Op Cell (Option ℕ × ℕ) :=
      fun acc => do
        let done ← isSome acc.1
        if done then pure acc else do
          let trial ← Arlib.Computation.Charged.repeatFor (fun _ (inner : ℕ × ℕ) => do
            let bit ← fairBit tape inner.2
            let value ← appendBit inner.1 bit
            let next ← successor inner.2
            pure (value, next)) ((v - 1).log2 + 1) (0, acc.2)
          let accepted ← lessThan trial.1 v
          if accepted then pure (some trial.1, trial.2)
          else pure (none, trial.2)
    have hstep (acc : Option ℕ × ℕ) :
        (step acc).val = if acc.1.isSome then acc else
          let word := readWord tape ((v - 1).log2 + 1) 0 acc.2
          if word.1 < v then (some word.1, word.2) else (none, word.2) := by
      rcases acc with ⟨value, cursor⟩
      cases value with
      | some value =>
          simp only [step, Arlib.Computation.Charged.val_bind, isSome,
            Arlib.Computation.Charged.val_op, Option.isSome_some,
            ite_true, Arlib.Computation.Charged.val_pure]
      | none =>
          simp only [step, Arlib.Computation.Charged.val_bind, isSome,
            Arlib.Computation.Charged.val_op, Option.isSome_none,
            Bool.false_eq_true, ite_false, readWord_charged]
          by_cases ha : (readWord tape ((v - 1).log2 + 1) 0 cursor).1 < v
          · simp only [lessThan, ha, decide_true, Arlib.Computation.Charged.val_op,
              ite_true, Arlib.Computation.Charged.val_pure]
          · simp only [lessThan, ha, decide_false, Arlib.Computation.Charged.val_op,
              Bool.false_eq_true, ite_false, Arlib.Computation.Charged.val_pure]
    have hfold (xs : List ℕ) (acc : Option ℕ × ℕ) :
        (Arlib.Computation.Charged.foldl (fun acc _ => step acc) xs acc).val =
          sampleWords tape v xs.length acc := by
      induction xs generalizing acc with
      | nil => rfl
      | cons x xs ih =>
          rw [Arlib.Computation.Charged.val_foldl_cons, hstep, ih]
          rfl
    have hbad : ¬ v < 1 := by omega
    have hsingle : ¬ v < 2 := by omega
    unfold boundedUniform
    simp only [Arlib.Computation.Charged.val_bind, lessThan, uniformWidth,
      Arlib.Computation.Charged.val_op, decide_eq_true_eq, hbad, hsingle,
      ite_false]
    simpa only [Arlib.Computation.Charged.repeatFor, List.length_range, step, lessThan] using
      hfold (List.range trials) (none, cursor)
  
/-- INTERNAL: Exhausting the sampler cap forces a true leading bit in
every trial word. This is a necessary event, not a claim of uniform output.
TEXLINE: main.tex:1392-1421 -/
theorem abort_forces_leading_bits (tape : ℕ → Bool) (trials v cursor : ℕ)
    (hv : 2 ≤ v)
    (habort : (boundedUniform tape trials v cursor).val.1 = none) :
    ∀ k < trials, tape (cursor + k * ((v - 1).log2 + 1)) = true := by
  rw [boundedUniform_value tape trials v cursor hv] at habort
  induction trials generalizing cursor with
  | zero => intro k hk; omega
  | succ trials ih =>
      simp only [sampleWords, Option.isSome_none, Bool.false_eq_true, ite_false] at habort
      have hrejected : ¬ (readWord tape ((v - 1).log2 + 1) 0 cursor).1 < v := by
        intro haccepted
        rw [if_pos haccepted, sampleWords_some] at habort
        contradiction
      rw [if_neg hrejected, readWord_cursor] at habort
      have hhead : tape cursor = true := by
        cases hbit : tape cursor with
        | false => exact False.elim (hrejected (false_leading_bit_accepts tape v cursor hv hbit))
        | true => rfl
      intro k hk
      cases k with
      | zero => simpa using hhead
      | succ k =>
          have ht := ih (cursor + ((v - 1).log2 + 1)) habort k (by omega)
          convert ht using 1
          congr 1
          ring

/-- INTERNAL: Forcing a set of distinct fair-bit coordinates leaves at most
one assignment for each choice of the other coordinates. -/
theorem forced_bits_card (t : ℕ) (forced : Finset (Fin t))
    (event : List.Vector Bool t → Prop)
    (hforced : ∀ bits, event bits → ∀ i ∈ forced, bits.get i = true) :
    letI := Classical.propDecidable
    (Finset.univ.filter event).card ≤ 2 ^ (t - forced.card) := by
  classical
  let free := {i : Fin t // i ∉ forced}
  let restrict : {bits : List.Vector Bool t // event bits} → (free → Bool) :=
    fun bits i => bits.val.get i.val
  have hinj : Function.Injective restrict := by
    intro a b h
    apply Subtype.ext
    apply List.Vector.ext
    intro i
    by_cases hi : i ∈ forced
    · rw [hforced a.val a.property i hi, hforced b.val b.property i hi]
    · exact congrFun h (⟨i, hi⟩ : free)
  have hcard := Fintype.card_le_of_injective restrict hinj
  have hfree : Fintype.card free = t - forced.card := by
    simp only [free, Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
  rw [Fintype.card_fun, hfree, Fintype.card_bool] at hcard
  simpa only [Fintype.card_subtype] using hcard

/-- INTERNAL: In a covered finite suffix, exhausting all integer-draw trials
forces one distinct true coordinate per trial, giving a Boolean-cylinder count.
TEXLINE: main.tex:1392-1421 -/
theorem abort_suffix_card (pref : List Bool) (trials v t : ℕ)
    (hv : 2 ≤ v) (hcoverage : trials * ((v - 1).log2 + 1) ≤ t) :
    Set.ncard {suffix : List Bool | suffix.length = t ∧
      (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
        trials v pref.length).val.1 = none} ≤ 2 ^ (t - trials) := by
  classical
  let width := (v - 1).log2 + 1
  let site : Fin trials → Fin t := fun k => ⟨k.val * width, by
    have hk := k.isLt
    dsimp only [width] at *
    nlinarith⟩
  let forced := Finset.univ.image site
  have hinj : Function.Injective site := by
    intro a b h
    have heq : a.val * width = b.val * width := congrArg Fin.val h
    apply Fin.ext
    dsimp only [width] at heq
    nlinarith
  have hcard : forced.card = trials := by
    rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin]
  rw [FiniteObservationMarkov.event_card_vectors]
  have hbound := forced_bits_card t forced (fun suffix =>
    (boundedUniform (fun i => ((pref ++ suffix.val)[i]?).getD false)
      trials v pref.length).val.1 = none) (by
    intro suffix habort i hi
    obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hi
    have hbits := abort_forces_leading_bits
      (fun i => ((pref ++ suffix.val)[i]?).getD false)
      trials v pref.length hv habort k.val k.isLt
    rw [List.getElem?_append_right (by omega), Nat.add_sub_cancel_left] at hbits
    have hlt : k.val * width < suffix.val.length := by
      rw [suffix.property]
      exact (site k).isLt
    change suffix.val[k.val * width]?.getD false = true at hbits
    rw [List.getElem?_eq_getElem hlt, Option.getD_some] at hbits
    exact hbits)
  simpa only [hcard] using hbound

/-- INTERNAL: The rejection cap of a positive-denominator draw has conditional
fair-suffix mass at most 2⁻ᵗʳⁱᵃˡˢ when the whole trial budget fits in the suffix.
The denominator and consumed prefix are fixed by the earlier history.
TEXLINE: main.tex:1392-1421 -/
theorem boundedUniform_abort_mass (pref : List Bool) (trials v t : ℕ)
    (hv : 0 < v) (hcoverage : trials * ((v - 1).log2 + 1) ≤ t) :
    (Set.ncard {suffix : List Bool | suffix.length = t ∧
      (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
        trials v pref.length).val.1 = none} : ℚ) / (2 : ℚ) ^ t ≤
      (1 / 2 : ℚ) ^ trials := by
  classical
  by_cases hsingle : v = 1
  · subst v
    have hempty : {suffix : List Bool | suffix.length = t ∧
        (boundedUniform (fun i => ((pref ++ suffix)[i]?).getD false)
          trials 1 pref.length).val.1 = none} = ∅ := by
      ext suffix
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨_, habort⟩
      simp only [boundedUniform, Arlib.Computation.Charged.val_bind,
        lessThan, Arlib.Computation.Charged.val_op, Nat.lt_irrefl,
        decide_false, Bool.false_eq_true, ite_false, Nat.lt_succ_self,
        decide_true, ite_true, Arlib.Computation.Charged.val_pure,
        Option.some_ne_none] at habort
    rw [hempty]
    simp only [Set.ncard_empty, Nat.cast_zero, zero_div]
    positivity
  · have hv₂ : 2 ≤ v := by omega
    have hcard := abort_suffix_card pref trials v t hv₂ hcoverage
    have htrials : trials ≤ t := by nlinarith
    have hbound : (2 : ℚ) ^ (t - trials) / (2 : ℚ) ^ t =
        (1 / 2 : ℚ) ^ trials := by
      have heq : t = (t - trials) + trials := by omega
      conv_lhs => arg 2; rw [heq, pow_add]
      rw [div_pow, one_pow]
      field_simp
    rw [← hbound]
    apply div_le_div_of_nonneg_right _ (by positivity)
    exact_mod_cast hcard

/-- INTERNAL: A finite stopping-prefix description of one adaptive integer
call, including the positive denominator fixed at that prefix and the coverage
needed to read every permitted rejection trial. Relative prefixes are taken
after the fixed earlier tape `base`.
TEXLINE: main.tex:1415-1421 -/
structure DrawHistory (base : List Bool) (t trials : ℕ) where
  prefixes : Finset (List Bool)
  denominator : List Bool → ℕ
  positive : ∀ head ∈ prefixes, 0 < denominator head
  length_le : ∀ head ∈ prefixes, head.length ≤ t
  prefix_free : ∀ a ∈ prefixes, ∀ b ∈ prefixes, a <+: b → a = b
  coverage : ∀ head ∈ prefixes,
    trials * ((denominator head - 1).log2 + 1) ≤ t - head.length

/-- INTERNAL: Actual rejection-cap aborts at the stopping prefixes of an
adaptive integer call. No synthetic randomness replaces the original tape. -/
def DrawHistory.abortEvent {base : List Bool} {t trials : ℕ}
    (history : DrawHistory base t trials) (bits : List Bool) : Prop :=
  ∃ head ∈ history.prefixes, head <+: bits ∧
    (boundedUniform (fun i => ((base ++ bits)[i]?).getD false)
      trials (history.denominator head) (base.length + head.length)).val.1 = none

/-- INTERNAL: A single adaptive draw has the same rejection-cap budget as a
fixed-denominator call: its stopping prefixes are disjoint, and the denominator
is fixed before its fresh trial bits are read. Coverage stays explicit.
TEXLINE: main.tex:1415-1421 -/
theorem adaptive_draw_abort_mass (base : List Bool) (t trials : ℕ)
    (history : DrawHistory base t trials) :
    (Set.ncard {bits : List Bool | bits.length = t ∧ history.abortEvent bits} : ENNReal) *
      (1 / 2 : ENNReal) ^ t ≤ (1 / 2 : ENNReal) ^ trials := by
  classical
  apply FiniteTapePrefixBound.finite_prefix_failure_bound t history.prefixes
    history.abortEvent ((1 / 2 : ENNReal) ^ trials)
    history.length_le history.prefix_free
  · intro bits _ he
    obtain ⟨head, hm, hp, _⟩ := he
    exact ⟨head, hm, hp⟩
  · intro head hhead
    let E := {suffix : List Bool | suffix.length = t - head.length ∧
      (boundedUniform (fun i => (((base ++ head) ++ suffix)[i]?).getD false)
        trials (history.denominator head) (base ++ head).length).val.1 = none}
    have hsub : {suffix : List Bool | suffix.length = t - head.length ∧
        history.abortEvent (head ++ suffix)} ⊆ E := by
      intro suffix hs
      obtain ⟨other, hother, hp, habort⟩ := hs.2
      have heq : other = head := by
        rcases List.prefix_or_prefix_of_prefix hp (List.prefix_append head suffix) with h | h
        · exact history.prefix_free other hother head hhead h
        · exact (history.prefix_free head hhead other hother h).symm
      subst other
      refine ⟨hs.1, ?_⟩
      simpa only [List.append_assoc, List.length_append] using habort
    have hfinite : E.Finite :=
      (List.finite_length_eq Bool (t - head.length)).subset (fun _ hs => hs.1)
    have hcard := Set.ncard_le_ncard hsub hfinite
    have hsingle := FiniteObservationMarkov.ennreal_mass_of_rat_bound
      (t - head.length) E.ncard ((1 / 2 : ℚ) ^ trials)
      (boundedUniform_abort_mass (base ++ head) trials (history.denominator head)
        (t - head.length) (history.positive head hhead) (history.coverage head hhead))
    have hhalf : ENNReal.ofReal (((1 / 2 : ℚ) ^ trials : ℚ) : ℝ) =
        (1 / 2 : ENNReal) ^ trials := by
      push_cast
      rw [ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2),
        ENNReal.ofReal_one, ENNReal.ofReal_ofNat]
    rw [hhalf] at hsingle
    exact (mul_le_mul_left (Nat.cast_le.mpr hcard) _).trans hsingle

end CountingMatroid.Analysis.BoundedUniformAbortMass

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r26 · proved · identified the charged word and rejection loops, proved that every aborted trial has a true leading bit, counted the distinct forced coordinates, and transferred the resulting cap bound to covered prefix-free adaptive histories.
-/
