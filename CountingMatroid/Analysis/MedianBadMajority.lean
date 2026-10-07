import CountingMatroid.Interface.Pseudocode

set_option autoImplicit false
namespace CountingMatroid.Analysis.MedianAmplification

/-- INTERNAL: A sorted prefix below a threshold contributes to the failure count. -/
private theorem countP_ge_of_sorted_getElem (xs : List ℚ) (lower : ℚ)
    (hord : xs.SortedLE) (k : ℕ) (hk : k < xs.length)
    (hval : xs[k] < lower) :
    k + 1 ≤ xs.countP (fun x => decide (x < lower)) := by
  have ht : ∀ x ∈ xs.take (k + 1), x < lower := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, heq⟩
    have hi' : i < xs.length := by
      have := (List.take_sublist (k+1) xs).length_le
      omega
    have hik : i ≤ k := by
      simp only [List.length_take] at hi
      omega
    have hix : xs[i] ≤ xs[k] := hord.getElem_le_getElem_of_le hik
    have hget : (xs.take (k+1))[i] = xs[i] := by simp
    rw [hget] at heq
    rw [heq] at hix
    exact lt_of_le_of_lt hix hval
  have hfilter : (xs.take (k+1)).filter (fun x => decide (x < lower)) = xs.take (k+1) := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true (ht x hx)
  have hc : (xs.take (k+1)).countP (fun x => decide (x < lower)) = k+1 := by
    rw [List.countP_eq_length_filter, hfilter, List.length_take]
    omega
  calc
    k+1 = (xs.take (k+1)).countP (fun x => decide (x < lower)) := hc.symm
    _ ≤ xs.countP (fun x => decide (x < lower)) := (List.take_sublist (k+1) xs).countP_le

/-- INTERNAL: A sorted suffix above a threshold contributes to the failure count. -/
private theorem countP_ge_of_sorted_getElem_right (xs : List ℚ) (upper : ℚ)
    (hord : xs.SortedLE) (k : ℕ) (hk : k < xs.length)
    (hval : upper < xs[k]) :
    xs.length - k ≤ xs.countP (fun x => decide (upper < x)) := by
  have ht : ∀ x ∈ xs.drop k, upper < x := by
    intro x hx
    rcases List.mem_iff_getElem.mp hx with ⟨i, hi, heq⟩
    have hij : k ≤ k+i := by omega
    have hi' : k+i < xs.length := by
      simp only [List.length_drop] at hi
      omega
    have hix : xs[k] ≤ xs[k+i] := hord.getElem_le_getElem_of_le hij
    have hget : (xs.drop k)[i] = xs[k+i] := by simp
    rw [hget] at heq
    rw [heq] at hix
    exact lt_of_lt_of_le hval hix
  have hfilter : (xs.drop k).filter (fun x => decide (upper < x)) = xs.drop k := by
    apply List.filter_eq_self.mpr
    intro x hx
    exact decide_eq_true (ht x hx)
  have hc : (xs.drop k).countP (fun x => decide (upper < x)) = xs.length-k := by
    rw [List.countP_eq_length_filter, hfilter, List.length_drop]
  calc
    xs.length-k = (xs.drop k).countP (fun x => decide (upper < x)) := hc.symm
    _ ≤ xs.countP (fun x => decide (upper < x)) := (List.drop_sublist k xs).countP_le

/-- INTERNAL: Pointwise implication makes a list predicate count monotone. -/
private theorem countP_le_of_imp {α : Type} (xs : List α) (p q : α → Bool)
    (h : ∀ x, p x = true → q x = true) : xs.countP p ≤ xs.countP q := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
      simp only [List.countP_cons]
      by_cases hp : p x = true
      · have hq := h x hp
        simp [hp, hq]
        exact ih
      · simp [hp]
        omega

/-- INTERNAL: A median outside the interval forces a strict majority of failures.
TEXLINE: main.tex:1455-1460 -/
theorem median_bad_implies_majority_bad (xs : List ℚ) (lower upper : ℚ)
    (hodd : Odd xs.length)
    (hbad : CountingMatroid.Interface.Pseudocode.median xs < lower ∨
      upper < CountingMatroid.Interface.Pseudocode.median xs) :
    xs.length / 2 + 1 ≤ xs.countP (fun x => decide (x < lower ∨ upper < x)) := by
  let ys := xs.insertionSort (· ≤ ·)
  have hlen : ys.length = xs.length := List.length_insertionSort _ _
  have hk : xs.length / 2 < ys.length := by
    rcases hodd with ⟨m, hm⟩
    omega
  have hmed : CountingMatroid.Interface.Pseudocode.median xs = ys[xs.length / 2] := by
    simp [CountingMatroid.Interface.Pseudocode.median, ys, List.getElem?_eq_getElem hk]
  have hsorted : ys.SortedLE := List.sortedLE_insertionSort
  have hcount : ys.countP (fun x => decide (x < lower ∨ upper < x)) =
      xs.countP (fun x => decide (x < lower ∨ upper < x)) :=
    (List.perm_insertionSort (· ≤ ·) xs).countP_eq _
  rw [hmed] at hbad
  rw [← hcount]
  rcases hbad with hlo | hhi
  · exact (countP_ge_of_sorted_getElem ys lower hsorted _ hk hlo).trans
      (countP_le_of_imp ys _ _ (by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; exact Or.inl hx))
  · have hge := countP_ge_of_sorted_getElem_right ys upper hsorted _ hk hhi
    have heq : ys.length - xs.length / 2 = xs.length / 2 + 1 := by
      rcases hodd with ⟨m, hm⟩
      omega
    rw [← heq]
    exact hge.trans
      (countP_le_of_imp ys _ _ (by intro x hx; simp only [decide_eq_true_eq] at hx ⊢; exact Or.inr hx))

end CountingMatroid.Analysis.MedianAmplification
