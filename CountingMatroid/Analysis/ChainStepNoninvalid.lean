import CountingMatroid.Analysis.ChainStepIntervalReplay

set_option autoImplicit false

/-!
A successful operational chain attempt preserves non-invalid classification.
An invalid proposal is rejected; each other success returns either the valid
old state or the proposal whose classifier was checked. This statement does
not claim that every failure is a capped draw failure.
-/

namespace CountingMatroid.Analysis.ChainStepNoninvalid

open CountingMatroid.Model CountingMatroid.Program

/-- INTERNAL: A successful attempt preserves non-invalid classification,
including rejected proposals and the lazy holding branch.
TEXLINE: main.tex:746-768 -/
theorem chainStep_noninvalid {n : ℕ} (r : ℕ)
    (o₁ o₂ : IndependenceOracle n) (tape : ℕ → Bool)
    (trials : ℕ) (q : ℚ) (weights : Multipliers n)
    (state : PairedSet n) (cursor : ℕ) (result : PairedSet n × ℕ)
    (hvalid : (classifyState state).val ≠ .invalid)
    (h : (chainStep r o₁ o₂ tape trials q weights state cursor).val = some result) :
    (classifyState result.1).val ≠ .invalid := by
  unfold chainStep at h
  simp only [Arlib.Computation.Charged.val_bind] at h
  split at h
  · have heq := Option.some.inj h
    rw [← heq]
    exact hvalid
  · simp only [Arlib.Computation.Charged.val_bind] at h
    split at h
    · cases h
    · simp only [Arlib.Computation.Charged.val_bind] at h
      split at h
      · cases h
      · simp only [Arlib.Computation.Charged.val_bind] at h
        split at h
        · simp only [Arlib.Computation.Charged.val_bind] at h
          split at h
          · have heq := Option.some.inj h
            rw [← heq]
            exact hvalid
          · rename_i kind hkind
            simp only [Arlib.Computation.Charged.val_bind] at h
            split at h
            · simp only [Arlib.Computation.Charged.val_bind] at h
              split at h
              · simp only [Arlib.Computation.Charged.val_bind] at h
                split at h
                · cases h
                · simp only [Arlib.Computation.Charged.val_bind] at h
                  split at h
                  all_goals
                    have heq := Option.some.inj h
                    rw [← heq]
                    first | exact hkind | exact hvalid
              · have heq := Option.some.inj h
                rw [← heq]
                exact hkind
            · cases h
        · cases h

end CountingMatroid.Analysis.ChainStepNoninvalid
