import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false

namespace CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: Recursively sample the independent outputs used by the median. -/
noncomputable def independentRuns {α : Type} (q : PMF α) : ℕ → PMF (List α)
  | 0 => pure []
  | m + 1 => do
      let x ← q
      let xs ← independentRuns q m
      pure (x :: xs)

/-- INTERNAL: Independent sampling always returns the prescribed number of values. -/
theorem independentRuns_support_length {α : Type} (q : PMF α) (m : ℕ)
    (xs : List α) (h : xs ∈ (independentRuns q m).support) : xs.length = m := by
  induction m generalizing xs with
  | zero =>
      change xs ∈ (PMF.pure ([] : List α)).support at h
      simpa using h
  | succ m ih =>
      change xs ∈ (q.bind fun x => (independentRuns q m).map (List.cons x)).support at h
      rw [PMF.mem_support_bind_iff] at h
      rcases h with ⟨x, hx, hs⟩
      rw [PMF.mem_support_map_iff] at hs
      rcases hs with ⟨rest, hrest, heq⟩
      subst xs
      simp [ih rest hrest]

end CountingMatroid.Analysis.MedianAmplification
