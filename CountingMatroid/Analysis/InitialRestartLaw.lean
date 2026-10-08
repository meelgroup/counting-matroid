import CountingMatroid.Analysis.FirstPhaseFailure
import Mathlib.Data.List.OfFn
import CountingMatroid.Analysis.BoundedRunPhaseHistory

set_option autoImplicit false

/-!
The phase-zero restart is exactly a fresh uniform transversal, with no return
excursion or restart-cap failure. The lemmas below retain the actual bit cursor
and the finite-tape suffix, rather than supplying a new random source.
-/

namespace CountingMatroid.Analysis.InitialRestartLaw

open CountingMatroid.Model CountingMatroid.Model.Operations CountingMatroid.Program

/-- INTERNAL: Split a charged fold's value at a list boundary. -/
private theorem foldl_append_value {α β : Type}
    (f : β → α → Arlib.Computation.Charged Op Cell β)
    (xs ys : List α) (initial : β) :
    (Arlib.Computation.Charged.foldl f (xs ++ ys) initial).val =
      (Arlib.Computation.Charged.foldl f ys
        (Arlib.Computation.Charged.foldl f xs initial).val).val := by
  induction xs generalizing initial with
  | nil => rfl
  | cons x xs ih =>
      simpa only [List.cons_append, Arlib.Computation.Charged.val_foldl_cons]
        using ih (f initial x).val

/-- INTERNAL: Evaluate the fresh-bit scan on an indexed list, including its
cursor movement and all elements inserted into the actual paired set.
TEXLINE: main.tex:1163-1176 -/
private theorem fresh_scan_value {n : ℕ} (tape : ℕ → Bool) (k : ℕ)
    (indices : Fin k → Fin n) (state : PairedSet n) (cursor : ℕ) :
    (Arlib.Computation.Charged.foldl (fun acc i => do
      let bit ← fairBit tape acc.2
      let state ← insertPaired acc.1 (i, bit)
      let next ← successor acc.2
      pure (state, next)) (List.ofFn indices) (state, cursor)).val =
      (state ∪ Finset.univ.image (fun i : Fin k => (indices i, tape (cursor + i))),
        cursor + k) := by
  induction k generalizing state cursor with
  | zero => simp
  | succ k ih =>
      rw [List.ofFn_succ', List.concat_eq_append]
      change (Arlib.Computation.Charged.foldl _
        (List.ofFn (fun i : Fin k => indices i.castSucc) ++ [indices (Fin.last k)])
          (state, cursor)).val = _
      rw [foldl_append_value, ih]
      simp only [Arlib.Computation.Charged.val_foldl_cons,
        Arlib.Computation.Charged.val_foldl_nil, Arlib.Computation.Charged.val_bind,
        fairBit, insertPaired, successor, Arlib.Computation.Charged.val_op,
        Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_pure]
      congr 1
      · rw [Fin.univ_castSuccEmb, Finset.cons_eq_insert, Finset.image_insert,
          Finset.map_eq_image, Finset.image_image]
        simp only [Fin.coe_castSuccEmb, Fin.val_last]
        simp only [Finset.union_insert]
        rfl

/-- PAPER: main.tex:1163-1176
A fresh restart reads precisely the next n bits and selects one element from
each pair. This equality also identifies the law when those bits are fair. -/
theorem freshTransversal_value (n : ℕ) (tape : ℕ → Bool) (cursor : ℕ) :
    (freshTransversal n tape cursor).val =
      (Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))), cursor + n) := by
  simpa only [freshTransversal, ← List.ofFn_id, Finset.empty_union, id_eq] using
    fresh_scan_value tape n id (∅ : PairedSet n) cursor

/-- PAPER: main.tex:1174-1176
The phase-zero restart cannot exhaust the restart cap or abort a trace draw. -/
theorem restartPhase_zero {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) (tables : LearnedWeights n)
    (cursor : ℕ) :
    (restartPhase r o₁ o₂ tape s tables 0 cursor).val =
      some (Finset.univ.image (fun i : Fin n => (i, tape (cursor + i))), cursor + n) := by
  simp only [restartPhase, Arlib.Computation.Charged.val_bind,
    freshTransversal_value, Arlib.Computation.Charged.repeatFor,
    List.range_zero, Arlib.Computation.Charged.val_foldl_nil,
    Arlib.Computation.Charged.val_pure]

/-- INTERNAL: Disintegrate a finite fair tape into its fixed-length prefix
and remaining suffix. Every prefix has the same number of possible suffixes;
no independence of adaptive algorithm events is assumed.
TEXLINE: main.tex:1207-1212,1415-1421 -/
theorem prefix_suffix_count (k t : ℕ) (event : List Bool → Prop) :
    Set.ncard {bits : List Bool | bits.length = k + t ∧ event bits} =
      ∑ headBits : List.Vector Bool k,
        Set.ncard {suffix : List Bool | suffix.length = t ∧ event (headBits.val ++ suffix)} := by
  classical
  let full := {bits : List Bool | bits.length = k + t ∧ event bits}
  let tails := fun headBits : List.Vector Bool k =>
    {suffix : List Bool | suffix.length = t ∧ event (headBits.val ++ suffix)}
  have ht (headBits : List.Vector Bool k) : (tails headBits).Finite :=
    (List.finite_length_eq Bool t).subset (fun _ h => h.1)
  let (headBits : List.Vector Bool k) : Finite (tails headBits) := (ht headBits).to_subtype
  let join : (Σ headBits : List.Vector Bool k, tails headBits) → full := fun pair =>
    ⟨pair.1.val ++ pair.2.val, by
      exact ⟨by rw [List.length_append, pair.1.property, pair.2.property.1],
        pair.2.property.2⟩⟩
  have hjoin : Function.Bijective join := by
    constructor
    · rintro ⟨headBits, suffix⟩ ⟨headBits', suffix'⟩ heq
      have heq' : headBits.val ++ suffix.val = headBits'.val ++ suffix'.val :=
        congrArg Subtype.val heq
      obtain ⟨hp, hs⟩ := List.append_inj heq' (headBits.property.trans headBits'.property.symm)
      have hp' : headBits = headBits' := Subtype.ext hp
      subst headBits'
      have hs' : suffix = suffix' := Subtype.ext hs
      subst suffix'
      rfl
    · rintro ⟨bits, hbits⟩
      change bits.length = k + t ∧ event bits at hbits
      let headBits : List.Vector Bool k :=
        ⟨bits.take k, List.length_take_of_le (by omega)⟩
      let suffix : tails headBits := ⟨bits.drop k, by
        refine ⟨?_, ?_⟩
        · simp only [List.length_drop, hbits.1, Nat.add_sub_cancel_left]
        · simpa only [headBits, List.take_append_drop] using hbits.2⟩
      refine ⟨⟨headBits, suffix⟩, ?_⟩
      apply Subtype.ext
      exact List.take_append_drop k bits
  change Nat.card full = ∑ headBits, Nat.card (tails headBits)
  rw [← Nat.card_sigma]
  exact Nat.card_congr (Equiv.ofBijective join hjoin).symm

/-- INTERNAL: Condition on a concrete earlier history, then read a fresh
fixed-length prefix. Its transversal depends exactly on that prefix, and the
following suffix remains untouched by the restart.
TEXLINE: main.tex:1207-1212 -/
theorem freshTransversal_after_prefix (n : ℕ) (history : List Bool)
    (headBits : List.Vector Bool n) (suffix : List Bool) :
    (freshTransversal n
      (fun i => ((history ++ headBits.val ++ suffix)[i]?).getD false)
      history.length).val =
      (Finset.univ.image (fun i : Fin n => (i, headBits.get i)), history.length + n) := by
  rw [freshTransversal_value]
  congr 1
  apply Finset.image_congr
  intro i _
  change (i, ((history ++ headBits.val ++ suffix)[history.length + i.val]?).getD false) =
    (i, headBits.get i)
  congr 1
  rw [List.append_assoc, List.getElem?_append_right (by omega)]
  simp only [Nat.add_sub_cancel_left]
  rw [List.getElem?_append_left (by simpa only [headBits.property] using i.isLt)]
  simp [List.Vector.get, headBits.property, i.isLt]

/-- INTERNAL: The deterministic continuation of phase zero after its fresh
restart. It evaluates the actual observation and finish subroutines, retaining
all of their abort branches and the actual learned-table update.
TEXLINE: main.tex:1177-1201 -/
noncomputable def initialPhaseResult {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool) (s : AnnealingSchedule)
    (start : PairedSet n × ℕ) : Option (AnnealingCursor n) :=
  let weights := (initialWeights n).val
  let tables := (allocateLearnedWeights n s.L weights).val
  match (observePhase r o₁ o₂ tape s 1 weights start).val with
  | none => none
  | some observed =>
      match (finishPhase s 0 weights observed).val with
      | none => none
      | some (ratio, nextWeights) =>
          if 1 < s.L then
            some ⟨(learnedWeightWrite tables 1 s.L nextWeights).val,
              nextWeights, ratio, observed.bitCursor⟩
          else some ⟨tables, nextWeights, ratio, observed.bitCursor⟩

/-- INTERNAL: Evaluate the actual initial phase by its restart-free continuation.
TEXLINE: main.tex:1163-1201 -/
theorem initial_phase_value {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (tape : ℕ → Bool) (s : AnnealingSchedule) :
    (BoundedRunPhase.boundedRunPhase r o₁ o₂ tape s 0
      (some (BoundedRunPhaseHistory.initialCursor n s))).val =
        initialPhaseResult r o₁ o₂ tape s
          (Finset.univ.image (fun i : Fin n => (i, tape i)), n) := by
  simp only [BoundedRunPhase.boundedRunPhase, BoundedRunPhaseHistory.initialCursor,
    Arlib.Computation.Charged.val_bind, ratPower, Arlib.Computation.Charged.repeatFor,
    List.range_zero, Arlib.Computation.Charged.val_foldl_nil,
    restartPhase_zero, zero_add, initialPhaseResult,
    successor, lessThan,
    initialWeights, allocateLearnedWeights, Arlib.Computation.Charged.val_opMany,
    ratMul, one_mul]
  cases hobs : (observePhase r o₁ o₂ tape s 1 (fun _ => 4)
    (Finset.univ.image (fun i : Fin n => (i, tape i)), n)).val with
  | none => simp only [Arlib.Computation.Charged.val_pure]
  | some observed =>
      simp only [Arlib.Computation.Charged.val_bind]
      cases hfin : (finishPhase s 0 (fun _ => 4) observed).val with
      | none => simp only [Arlib.Computation.Charged.val_pure]
      | some pair =>
          rcases pair with ⟨ratio, nextWeights⟩
          simp only [Arlib.Computation.Charged.val_bind,
            Arlib.Computation.Charged.val_opMany, Arlib.Computation.Charged.val_op]
          by_cases hup : 1 < s.L <;> simp [hup]

/-- INTERNAL: A certificate for the actual initial observation trajectory,
with its specified fresh starting transversal and its remaining finite tape.
TEXLINE: main.tex:1207-1212,1257-1285 -/
def InitialObservationCertificate {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (tape : ℕ → Bool)
    (state : PairedSet n) : Prop :=
  let C := fun a => TransversalPartition.partitionSum r o₁ o₂ (s.ρ ^ a)
  ∃ ratio : ℚ,
    (1 - s.η) / (1 + s.η) ≤ ratio / (C 1 / C 0) ∧
    ratio / (C 1 / C 0) ≤ (1 + s.η) / (1 - s.η) ∧
    ∃ next : AnnealingCursor n,
      initialPhaseResult r o₁ o₂ tape s (state, n) = some next ∧
      next.product = ratio ∧
      FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s 0
        (BoundedRunPhaseHistory.initialCursor n s) ∧
      (1 < s.L → FirstPhaseFailure.GoodStoredMultipliers r o₁ o₂ s 1 next)

/-- INTERNAL: The first failure at phase zero is precisely failure of the
observation certificate, because its restart is the fresh transversal and
has no return-time cap to exhaust.
TEXLINE: main.tex:1174-1176,1253-1285 -/
theorem firstFailure_zero_iff {n : ℕ} (r : ℕ) (o₁ o₂ : IndependenceOracle n)
    (s : AnnealingSchedule) (tape : ℕ → Bool) :
    FirstPhaseFailure.FirstFailure r o₁ o₂ tape s 0 ↔
      ¬ InitialObservationCertificate r o₁ o₂ s tape
        (Finset.univ.image (fun i : Fin n => (i, tape i))) := by
  simp only [FirstPhaseFailure.FirstFailure, Nat.not_lt_zero, IsEmpty.forall_iff,
    forall_const, true_and]
  apply not_congr
  constructor
  · rintro ⟨ratio, hl, hu, current, next, hcurrent, hnext, hmul, hgood, hnextgood⟩
    change some (BoundedRunPhaseHistory.initialCursor n s) = some current at hcurrent
    have heq := Option.some.inj hcurrent
    subst current
    refine ⟨ratio, hl, hu, next, ?_, ?_, hgood, hnextgood⟩
    · rwa [← initial_phase_value]
    · simpa only [BoundedRunPhaseHistory.initialCursor, one_mul] using hmul
  · rintro ⟨ratio, hl, hu, next, hnext, hmul, hgood, hnextgood⟩
    refine ⟨ratio, hl, hu, BoundedRunPhaseHistory.initialCursor n s, next,
      rfl, ?_, ?_, hgood, hnextgood⟩
    · rwa [initial_phase_value]
    · simpa only [BoundedRunPhaseHistory.initialCursor, one_mul] using hmul


/-- INTERNAL: Disintegrate the initial first-failure event using its actual
uniform fresh transversal and the untouched observation suffix. The statement
is an identity of counts; it does not assume an observation error estimate.
TEXLINE: main.tex:1207-1212,1253-1285 -/
theorem initial_failure_count_split {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (t : ℕ) :
    Set.ncard {bits : List Bool | bits.length = n + t ∧
      FirstPhaseFailure.FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s 0} =
    ∑ headBits : List.Vector Bool n,
      Set.ncard {suffix : List Bool | suffix.length = t ∧
        ¬ InitialObservationCertificate r o₁ o₂ s
          (fun i => ((headBits.val ++ suffix)[i]?).getD false)
          (Finset.univ.image (fun i : Fin n => (i, headBits.get i)))} := by
  classical
  rw [prefix_suffix_count]
  apply Finset.sum_congr rfl
  intro headBits _
  apply congrArg Set.ncard
  ext suffix
  change (suffix.length = t ∧ FirstPhaseFailure.FirstFailure r o₁ o₂
    (fun i => ((headBits.val ++ suffix)[i]?).getD false) s 0) ↔
    (suffix.length = t ∧ ¬ InitialObservationCertificate r o₁ o₂ s
      (fun i => ((headBits.val ++ suffix)[i]?).getD false)
      (Finset.univ.image (fun i : Fin n => (i, headBits.get i))))
  rw [firstFailure_zero_iff]
  have hstart := freshTransversal_after_prefix n [] headBits suffix
  rw [freshTransversal_value] at hstart
  simp only [List.nil_append, List.length_nil, zero_add] at hstart
  rw [show Finset.univ.image
      (fun i : Fin n => (i, ((headBits.val ++ suffix)[i.val]?).getD false)) =
      Finset.univ.image (fun i : Fin n => (i, headBits.get i)) from
    congrArg Prod.fst hstart]

/-- INTERNAL: The initial failure probability is the uniform average of its
conditional observation-suffix probabilities. This couples the base phase to
the actual finite block, with the default outside that same block retained.
TEXLINE: main.tex:1207-1212,1253-1285,1392-1421 -/
theorem initial_failure_mass_split {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (s : AnnealingSchedule) (t : ℕ) :
    (Set.ncard {bits : List Bool | bits.length = n + t ∧
      FirstPhaseFailure.FirstFailure r o₁ o₂ (fun i => (bits[i]?).getD false) s 0}
      : ENNReal) * (1 / 2 : ENNReal) ^ (n + t) =
    (1 / 2 : ENNReal) ^ n *
      ∑ headBits : List.Vector Bool n,
        (Set.ncard {suffix : List Bool | suffix.length = t ∧
          ¬ InitialObservationCertificate r o₁ o₂ s
            (fun i => ((headBits.val ++ suffix)[i]?).getD false)
            (Finset.univ.image (fun i : Fin n => (i, headBits.get i)))}
          : ENNReal) * (1 / 2 : ENNReal) ^ t := by
  rw [initial_failure_count_split, Nat.cast_sum, pow_add,
    Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro _ _
  ac_rfl

end CountingMatroid.Analysis.InitialRestartLaw

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r19 · proved · evaluated the actual fresh-bit scan and phase-zero restart,
  split finite tapes into equally weighted prefixes and observation suffixes,
  and derived the exact initial certificate-failure mass identity. No chain
  concentration bound, extra hypothesis, or unproved declaration introduced.
-/
