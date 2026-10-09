import CountingMatroid.Analysis.BoundedUniformAbortMass

set_option autoImplicit false

/-!
A deterministic stopping descriptor separates operational replay from the
finite prefix-free packaging required by the adaptive draw mass bound.
-/
namespace CountingMatroid.Analysis.StoppedDrawHistory

/-- INTERNAL: One partial pre-draw descriptor on fixed-length suffixes.
Replay fixes both the consumed relative prefix and the denominator before
reading any trial bits. TEXLINE: main.tex:1415-1421 -/
structure StoppedDraw (t trials : ℕ) where
  site : List Bool → Option (List Bool × ℕ)
  isPrefix : ∀ bits head v, bits.length = t → site bits = some (head, v) → head <+: bits
  stable : ∀ bits other head v, bits.length = t → other.length = t →
    site bits = some (head, v) → head <+: other → site other = some (head, v)
  positive : ∀ bits head v, bits.length = t → site bits = some (head, v) → 0 < v
  coverage : ∀ bits head v, bits.length = t → site bits = some (head, v) →
    trials * ((v - 1).log2 + 1) ≤ t - head.length

/-- INTERNAL: Finite stopping descriptors produce covered prefix-free draw
histories, preserving every actual descriptor and its denominator.
TEXLINE: main.tex:1415-1421 -/
theorem stopped_draw_history (base : List Bool) (t trials : ℕ)
    (draw : StoppedDraw t trials) :
    ∃ history : BoundedUniformAbortMass.DrawHistory base t trials,
      ∀ bits head v, bits.length = t → draw.site bits = some (head, v) →
        head ∈ history.prefixes ∧ history.denominator head = v ∧ head <+: bits := by
  classical
  let P : Set (List Bool) := {head | ∃ bits, bits.length = t ∧
    ∃ v, draw.site bits = some (head, v)}
  have hfinite : P.Finite := by
    apply ((List.finite_length_eq Bool t).image
      (fun bits => ((draw.site bits).getD ([], 0)).1)).subset
    rintro head ⟨bits, hlen, v, hs⟩
    exact ⟨bits, hlen, by simp only [hs, Option.getD_some]⟩
  have hw (head : List Bool) (h : head ∈ P) :
      ∃ v, ∃ bits, bits.length = t ∧ draw.site bits = some (head, v) := by
    obtain ⟨bits, hlen, v, hs⟩ := h
    exact ⟨v, bits, hlen, hs⟩
  let den := fun head => if h : head ∈ P then Classical.choose (hw head h) else 1
  have hd (head : List Bool) (h : head ∈ P) :
      ∃ bits, bits.length = t ∧ draw.site bits = some (head, den head) := by
    dsimp only [den]
    rw [dif_pos h]
    exact Classical.choose_spec (hw head h)
  have heq (bits head : List Bool) (v : ℕ) (hlen : bits.length = t)
      (hs : draw.site bits = some (head, v)) : den head = v := by
    have hm : head ∈ P := ⟨bits, hlen, v, hs⟩
    obtain ⟨other, ho, hsite⟩ := hd head hm
    have hr := draw.stable other bits head (den head) ho hlen hsite
      (draw.isPrefix bits head v hlen hs)
    exact (Prod.mk.inj (Option.some.inj (hr.symm.trans hs))).2
  refine ⟨⟨hfinite.toFinset, den, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro head hm
    obtain ⟨bits, hlen, hs⟩ := hd head (hfinite.mem_toFinset.mp hm)
    exact draw.positive bits head (den head) hlen hs
  · intro head hm
    obtain ⟨bits, hlen, hs⟩ := hd head (hfinite.mem_toFinset.mp hm)
    exact (draw.isPrefix bits head (den head) hlen hs).length_le.trans_eq hlen
  · intro a ha b hb hab
    obtain ⟨bitsA, hA, hsA⟩ := hd a (hfinite.mem_toFinset.mp ha)
    obtain ⟨bitsB, hB, hsB⟩ := hd b (hfinite.mem_toFinset.mp hb)
    have hr := draw.stable bitsA bitsB a (den a) hA hB hsA
      (hab.trans (draw.isPrefix bitsB b (den b) hB hsB))
    exact (Prod.mk.inj (Option.some.inj (hr.symm.trans hsB))).1
  · intro head hm
    obtain ⟨bits, hlen, hs⟩ := hd head (hfinite.mem_toFinset.mp hm)
    exact draw.coverage bits head (den head) hlen hs
  · intro bits head v hlen hs
    exact ⟨hfinite.mem_toFinset.mpr ⟨bits, hlen, v, hs⟩,
      heq bits head v hlen hs, draw.isPrefix bits head v hlen hs⟩

end CountingMatroid.Analysis.StoppedDrawHistory

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* 2026-10-09 · proved · finite stopping descriptors yield prefix-free covered histories; replay determines a unique denominator on each prefix.
-/
