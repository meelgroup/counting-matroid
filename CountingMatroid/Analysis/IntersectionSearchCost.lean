import CountingMatroid.Analysis.IntersectionSearch

set_option autoImplicit false

/-!
Uniform resource obligation for the concrete capped exchange-graph solver.
The proved bound composes table and fold accounting through graph construction,
frozen breadth-first layers, sink selection, and at most `n` toggles, then
through the `r`-round solver.
It is independent of all matroid and exact-oracle promises.
-/

namespace CountingMatroid.Analysis.IntersectionSearchCost

open CountingMatroid.Model CountingMatroid.Model.Operations
open CountingMatroid.Model.Subroutines
open CountingMatroid.Analysis.IntersectionSearch

/-- INTERNAL: Every single-currency batch contributes at most its batch size
to any coordinate of the charged cost vector. -/
theorem cost_opMany_le {α : Type} (instruction : Op) (amount : ℕ) (value : α)
    (op : Op) :
    (Arlib.Computation.Charged.opMany instruction amount value :
      Arlib.Computation.Charged Op Cell α).cost op ≤ amount := by
  simp only [Arlib.Computation.Charged.cost_opMany, Arlib.Computation.CostVec.many]
  split_ifs <;> omega

/-- INTERNAL: A uniform coordinate bound on each body controls a charged fold. -/
theorem cost_foldl_le {α β : Type} (f : β → α → Arlib.Computation.Charged Op Cell β)
    (l : List α) (k : ℕ) (hf : ∀ b a op, (f b a).cost op ≤ k)
    (b : β) (op : Op) :
    (Arlib.Computation.Charged.foldl f l b).cost op ≤ l.length * k := by
  induction l generalizing b with
  | nil => simp
  | cons a l ih =>
    rw [Arlib.Computation.Charged.cost_foldl_cons]
    simp only [Pi.add_apply, List.length_cons]
    have hhead := hf b a op
    have htail := ih (f b a).val
    nlinarith

/-- INTERNAL: Materializing a table pays allocation, all entry evaluations,
and all charged overwrites; the bound holds for every starting oracle. -/
theorem cost_tabulate_le {n : ℕ} {α : Type} [Inhabited α]
    (width k : ℕ) (f : Fin n → Arlib.Computation.Charged Op Cell α)
    (hf : ∀ i op, (f i).cost op ≤ k) (op : Op) :
    (tabulate width f).cost op ≤
      (n * width + 1) + n * (k + (n * width + 1)) := by
  let step := fun (table : Fin n → α) (i : Fin n) => do
    let value ← f i
    Arlib.Computation.Charged.opMany (Op.word .store) (n * width + 1)
      (Function.update table i value)
  have hstep (table : Fin n → α) (i : Fin n) (op : Op) :
      (step table i).cost op ≤ k + (n * width + 1) := by
    simp only [step, Arlib.Computation.Charged.cost_bind, Pi.add_apply]
    exact Nat.add_le_add (hf i op) (cost_opMany_le _ _ _ _)
  have hfold := cost_foldl_le step (List.finRange n)
    (k + (n * width + 1)) hstep
    (fun _ => (default : α)) op
  simp only [List.length_finRange] at hfold
  unfold tabulate
  simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply,
    Arlib.Computation.Charged.val_opMany]
  exact Nat.add_le_add (cost_opMany_le _ _ _ _) hfold

/-- INTERNAL: Uniform coordinate bound for the charged insertion tests. -/
theorem cost_testTerminal_le {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (i : Fin n) (op : Op) :
    (testTerminal o₁ o₂ I i).cost op ≤ n * (n + 1) + n + 6 := by
  simp [testTerminal, containsElement, insertElement, encodeQuery, oracleQuery,
    Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many]
  split_ifs <;> omega

/-- INTERNAL: Uniform coordinate bound for both oriented exchange tests. -/
theorem cost_testEdge_le {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (u v : Fin n) (op : Op) :
    (testEdge o₁ o₂ I u v).cost op ≤ 2 * (n * (n + 1)) + 4 * (n + 1) + 9 := by
  simp [testEdge, containsElement, insertElement, encodeQuery, oracleQuery,
    Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many]
  split_ifs <;> omega

/-- INTERNAL: A predecessor scan either retains a found path or pays for
one bounded path-table read, edge read, and capped path write. -/
theorem cost_predecessorStep_le {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (v : Fin n) (found : Option (List (Fin n))) (u : Fin n) (op : Op) :
    (predecessorStep g previous v found u).cost op ≤
      n * (n + 1) + n * n + n + 4 := by
  cases found <;> cases hp : previous u <;> cases he : g.edges u v <;>
    simp [predecessorStep, isSome, hp, he,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> omega

/-- INTERNAL: A vertex relaxation scans at most `n` predecessors. -/
theorem cost_relaxVertex_le {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (v : Fin n) (op : Op) :
    (relaxVertex g previous v).cost op ≤
      n * (n + 1) + 2 + n * (n * (n + 1) + n * n + n + 4) := by
  have hfold := cost_foldl_le (predecessorStep g previous v) (List.finRange n)
    (n * (n + 1) + n * n + n + 4)
    (fun found u op => cost_predecessorStep_le g previous v found u op) none op
  simp only [List.length_finRange] at hfold
  cases hp : previous v <;>
    simp [relaxVertex, isSome, hp,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> omega

/-- INTERNAL: Sink selection charges its bounded table and length scans. -/
theorem cost_sinkStep_le {n : ℕ} (g : ExchangeGraph n) (paths : Paths n)
    (best : Option (List (Fin n))) (i : Fin n) (op : Op) :
    (sinkStep g paths best i).cost op ≤ n * (n + 1) + 5 * n + 6 := by
  cases ht : (g.terminals i).2 <;> cases hp : paths i <;> cases best <;>
    simp [sinkStep, lessThan, ht, hp,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> (try simp only [Arlib.Computation.Charged.cost_pure, Pi.zero_apply]) <;> omega

/-- INTERNAL: Toggling an element pays membership and one bounded update. -/
theorem cost_toggle_le {n : ℕ} (I : Finset (Fin n)) (i : Fin n) (op : Op) :
    (toggle I i).cost op ≤ 2 * (n + 1) := by
  by_cases hi : i ∈ I <;>
    simp [toggle, containsElement, insertElement, hi,
      Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
    split_ifs <;> omega

/-- INTERNAL: Graph construction has a uniform quartic coordinate bound. -/
theorem cost_buildGraph_le {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (op : Op) :
    (buildGraph o₁ o₂ I).cost op ≤ 20 * (n + 1) ^ 4 := by
  have ht := cost_tabulate_le 2 (n * (n + 1) + n + 6)
    (testTerminal o₁ o₂ I) (fun i op => cost_testTerminal_le o₁ o₂ I i op) op
  have hr (u : Fin n) (op : Op) := cost_tabulate_le 1
    (2 * (n * (n + 1)) + 4 * (n + 1) + 9) (testEdge o₁ o₂ I u)
    (fun v op => cost_testEdge_le o₁ o₂ I u v op) op
  have he := cost_tabulate_le (n + 1)
    ((n * 1 + 1) + n * ((2 * (n * (n + 1)) + 4 * (n + 1) + 9) + (n * 1 + 1)))
    (fun u => tabulate 1 (testEdge o₁ o₂ I u)) hr op
  simp only [buildGraph, Arlib.Computation.Charged.cost_bind, Pi.add_apply,
    Arlib.Computation.Charged.cost_pure, Pi.zero_apply, Nat.add_zero]
  exact (Nat.add_le_add ht he).trans (by nlinarith)

/-- INTERNAL: Allocating and initializing source paths costs cubically. -/
theorem cost_initialPaths_le {n : ℕ} (g : ExchangeGraph n) (op : Op) :
    (initialPaths g).cost op ≤ 10 * (n + 1) ^ 3 := by
  have hbody (i : Fin n) (op : Op) :
      (do
        let terminal ← Arlib.Computation.Charged.opMany (Op.word .load) (2 * n + 1)
          (g.terminals i)
        if terminal.1 then
          Arlib.Computation.Charged.op (Op.word .store) (some [i])
        else pure none : Arlib.Computation.Charged Op Cell (Option (List (Fin n)))).cost op ≤
          2 * n + 2 := by
    cases ht : (g.terminals i).1 <;>
      simp [ht, Arlib.Computation.CostVec.one, Arlib.Computation.CostVec.many] <;>
      split_ifs <;> omega
  have h := cost_tabulate_le (n + 1) (2 * n + 2) _ hbody op
  exact h.trans (by nlinarith)

/-- INTERNAL: One frozen breadth-first layer has a quartic coordinate bound. -/
theorem cost_relaxPaths_le {n : ℕ} (g : ExchangeGraph n) (previous : Paths n)
    (op : Op) : (relaxPaths g previous).cost op ≤ 10 * (n + 1) ^ 4 := by
  have h := cost_tabulate_le (n + 1)
    (n * (n + 1) + 2 + n * (n * (n + 1) + n * n + n + 4))
    (relaxVertex g previous) (fun v op => cost_relaxVertex_le g previous v op) op
  exact h.trans (by nlinarith)

/-- INTERNAL: Capped breadth-first search and shortest sink selection cost
at most a fixed quintic polynomial, regardless of the graph's origin. -/
theorem cost_findPath_le {n : ℕ} (g : ExchangeGraph n) (op : Op) :
    (findPath g).cost op ≤ 30 * (n + 1) ^ 5 := by
  have hinit := cost_initialPaths_le g op
  have hlayers (paths : Paths n) := cost_foldl_le
    (fun paths (_ : ℕ) => relaxPaths g paths) (List.range n)
    (10 * (n + 1) ^ 4) (fun paths _ op => cost_relaxPaths_le g paths op) paths op
  have hsinks (paths : Paths n) := cost_foldl_le (sinkStep g paths) (List.finRange n)
    (n * (n + 1) + 5 * n + 6)
    (fun best i op => cost_sinkStep_le g paths best i op) none op
  simp only [List.length_range] at hlayers
  simp only [List.length_finRange] at hsinks
  have h35 : (n + 1) ^ 3 ≤ (n + 1) ^ 5 :=
    pow_le_pow_right₀ (by omega) (by omega)
  have hlayerSize : n * (10 * (n + 1) ^ 4) ≤ 10 * (n + 1) ^ 5 := by
    calc
      _ = 10 * (n * (n + 1) ^ 4) := by ring
      _ ≤ 10 * ((n + 1) * (n + 1) ^ 4) := by gcongr; omega
      _ = 10 * (n + 1) ^ 5 := by ring
  have hsinkSize : n * (n * (n + 1) + 5 * n + 6) ≤ 10 * (n + 1) ^ 3 := by
    nlinarith
  unfold findPath
  simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  calc
    _ ≤ 10 * (n + 1) ^ 3 +
        (n * (10 * (n + 1) ^ 4) + n * (n * (n + 1) + 5 * n + 6)) :=
      Nat.add_le_add hinit (Nat.add_le_add (hlayers _) (hsinks _))
    _ ≤ 30 * (n + 1) ^ 5 := by nlinarith

/-- INTERNAL: One augmentation builds a graph, searches it, and toggles
at most `n` elements; its bound needs no oracle correctness hypothesis. -/
theorem cost_augmentOnce_le {n : ℕ} (o₁ o₂ : IndependenceOracle n)
    (I : Finset (Fin n)) (op : Op) :
    (augmentOnce o₁ o₂ I).cost op ≤ 60 * (n + 1) ^ 5 := by
  have hgraph := cost_buildGraph_le o₁ o₂ I op
  have hpath := cost_findPath_le (buildGraph o₁ o₂ I).val op
  have htoggle (p : List (Fin n)) := cost_foldl_le toggle (p.take n)
    (2 * (n + 1)) (fun I i op => cost_toggle_le I i op) I op
  have htoggle' (p : List (Fin n)) :
      (Arlib.Computation.Charged.foldl toggle (p.take n) I).cost op ≤
        n * (2 * (n + 1)) :=
    (htoggle p).trans (Nat.mul_le_mul_right _ (List.length_take_le n p))
  have h45 : (n + 1) ^ 4 ≤ (n + 1) ^ 5 :=
    pow_le_pow_right₀ (by omega) (by omega)
  have htoggleSize : n * (2 * (n + 1)) ≤ 2 * (n + 1) ^ 5 := by
    calc
      _ = 2 * (n * (n + 1)) := by ring
      _ ≤ 2 * ((n + 1) * (n + 1)) := by gcongr; omega
      _ = 2 * (n + 1) ^ 2 := by ring
      _ ≤ 2 * (n + 1) ^ 5 := Nat.mul_le_mul_left 2
        (pow_le_pow_right₀ (by omega) (by omega))
  unfold augmentOnce
  simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply]
  cases hp : (findPath (buildGraph o₁ o₂ I).val).val with
  | none =>
    simp only [Arlib.Computation.Charged.cost_pure, Pi.zero_apply, Nat.add_zero]
    exact (Nat.add_le_add hgraph hpath).trans (by nlinarith)
  | some p =>
    exact (Nat.add_le_add hgraph (Nat.add_le_add hpath (htoggle' p))).trans
      (by nlinarith)

/-- INTERNAL: The explicit solver has fixed polynomial cost coefficients,
uniform even for oracle functions that are not matroid independence oracles.
TEXLINE: main.tex:283-289 -/
theorem intersectionSolver_bounded :
    FeasibilityBounded intersectionSolver 100000 8 100000 8 := by
  intro n r o₁ o₂
  have hcoordinate (op : Op) :
      (intersectionSolver.run n r o₁ o₂).cost op ≤ 1000 * (n + r + 1) ^ 8 := by
    have hfold := cost_foldl_le
      (fun I (_ : ℕ) => augmentOnce o₁ o₂ I) (List.range r)
      (60 * (n + 1) ^ 5) (fun I _ op => cost_augmentOnce_le o₁ o₂ I op)
      (∅ : Finset (Fin n)) op
    simp only [List.length_range] at hfold
    have hsize : 1 ≤ n + r + 1 := by omega
    have hproduct : r * (n + 1) ^ 5 ≤ (n + r + 1) ^ 6 := by
      calc
        _ ≤ (n + r + 1) * (n + r + 1) ^ 5 := by gcongr <;> omega
        _ = (n + r + 1) ^ 6 := by ring
    have h68 : (n + r + 1) ^ 6 ≤ (n + r + 1) ^ 8 :=
      pow_le_pow_right₀ hsize (by omega)
    have hloopBound := Nat.mul_le_mul_left 60 (hproduct.trans h68)
    have hloadSize : n + 1 ≤ (n + r + 1) ^ 8 := by
      calc
        _ ≤ n + r + 1 := by omega
        _ ≤ (n + r + 1) ^ 8 := by
          simpa only [pow_one] using pow_le_pow_right₀ hsize (by omega : 1 ≤ 8)
    have hunit : 1 ≤ (n + r + 1) ^ 8 := one_le_pow₀ hsize
    have heq : Arlib.Computation.CostVec.one (Op.word .eq) op ≤ 1 := by
      simp only [Arlib.Computation.CostVec.one]
      split_ifs <;> omega
    unfold intersectionSolver
    simp only [Arlib.Computation.Charged.cost_bind, Pi.add_apply,
      Arlib.Computation.Charged.val_opMany, natEqual,
      Arlib.Computation.Charged.cost_op]
    calc
      _ ≤ r * (60 * (n + 1) ^ 5) + (n + 1 + 1) :=
        Nat.add_le_add hfold (Nat.add_le_add (cost_opMany_le _ _ _ _) heq)
      _ ≤ 1000 * (n + r + 1) ^ 8 := by nlinarith

  constructor
  · have hfirst := hcoordinate Op.oracleFirst
    have hsecond := hcoordinate Op.oracleSecond
    dsimp [oracleCalls]
    nlinarith
  · have hfold (l : List Arlib.Computation.Op) (acc : ℕ) :
        l.foldl (fun total instruction => total +
          (intersectionSolver.run n r o₁ o₂).cost (Op.word instruction)) acc ≤
          acc + l.length * (1000 * (n + r + 1) ^ 8) := by
      induction l generalizing acc with
      | nil => simp
      | cons instruction l ih =>
        simp only [List.foldl_cons, List.length_cons]
        have hhead := hcoordinate (Op.word instruction)
        have htail := ih (acc + (intersectionSolver.run n r o₁ o₂).cost
          (Op.word instruction))
        nlinarith
    have hwords := hfold Arlib.Computation.Op.all 0
    have hlength : Arlib.Computation.Op.all.length = 20 := rfl
    rw [hlength, Nat.zero_add] at hwords
    have hbit := hcoordinate Op.fairBit
    dsimp [otherSteps]
    nlinarith

end CountingMatroid.Analysis.IntersectionSearchCost

/-! ### Run record
Newest first. History, not instruction — what this file claims is above.

* r16 · proved · closed the unconditional cost certificate by coordinate bounds through table construction, capped search, toggles, and the rank-many loop; no oracle promise is used.
-/
