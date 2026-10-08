import Arlib.MarkovChains.Techniques.Dirichlet

set_option autoImplicit false

/-!
Finite covariance sums for reversible positive semidefinite chains. The
finite geometric sum replaces the inverse and infinite series in the paper,
so the argument also applies to stationary laws with zero-weight states.
-/
namespace CountingMatroid.Analysis.StationaryCovarianceSum

open Arlib.Probability Arlib.Probability.FinDist Arlib.MarkovChains

variable {Ω : Type} [Fintype Ω] [DecidableEq Ω]

/-- INTERNAL: Composition of the iterated actions, used to transfer powers
between the two arguments of the stationary inner product.
TEXLINE: main.tex:1002-1009 -/
theorem act_iter_add (P : FinChain Ω) (f : Ω → ℝ) (s t : ℕ) :
    (P.iter (s + t)).act f = (P.iter s).act ((P.iter t).act f) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [Nat.succ_add, FinKernel.act_iter_succ, ih, FinKernel.act_iter_succ]

/-- INTERNAL: Reversibility moves an iterated action across the inner product.
TEXLINE: main.tex:1002-1009 -/
theorem ip_iter_transfer {π : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible π P) (f g : Ω → ℝ) (t : ℕ) :
    ip π f ((P.iter t).act g) = ip π ((P.iter t).act f) g := by
  induction t generalizing f with
  | zero => simp
  | succ t ih =>
    rw [FinKernel.act_iter_succ, ip_act_comm hrev, ip_comm π]
    rw [ih]
    have hcomm : (P.iter t).act (P.act f) = P.act ((P.iter t).act f) := by
      have h := act_iter_add P f t 1
      calc
        _ = (P.iter (t + 1)).act f := by simpa [FinKernel.act_iter_succ] using h.symm
        _ = _ := FinKernel.act_iter_succ P t f
    rw [hcomm, FinKernel.act_iter_succ]

/-- INTERNAL: Every stationary covariance of a reversible PSD chain is
nonnegative; even powers are squared norms and odd powers use PSD.
TEXLINE: main.tex:1002-1009 -/
theorem covariance_nonneg {π : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible π P) (hpsd : NonnegDefinite π P)
    (g : Ω → ℝ) (t : ℕ) : 0 ≤ ip π g ((P.iter t).act g) := by
  obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' t
  · rw [hk, two_mul, act_iter_add, ip_iter_transfer hrev]
    exact ip_self_nonneg π _
  · rw [hk, show 2 * k + 1 = k + (k + 1) by omega,
      act_iter_add, ip_iter_transfer hrev, FinKernel.act_iter_succ]
    exact hpsd _

/-- INTERNAL: The finite geometric action telescopes, with no inverse or
irreducibility assumption.
TEXLINE: main.tex:992-1009 -/
theorem geometric_action_sub (P : FinChain Ω) (g : Ω → ℝ) (N : ℕ) :
    (fun x => ∑ t ∈ Finset.range N, (P.iter t).act g x) -
      P.act (fun x => ∑ t ∈ Finset.range N, (P.iter t).act g x) =
        g - (P.iter N).act g := by
  have hact : ∀ N : ℕ,
      P.act (fun x => ∑ t ∈ Finset.range N, (P.iter t).act g x) =
        fun x => ∑ t ∈ Finset.range N, (P.iter (t + 1)).act g x := by
    intro N
    funext x
    change (∑ y, P x y * ∑ t ∈ Finset.range N, (P.iter t).act g y) = _
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro t _
    exact (congrFun (FinKernel.act_iter_succ P t g) x).symm
  rw [hact]
  funext x
  simp only [Pi.sub_apply]
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    linarith

/-- INTERNAL: A restricted dual energy estimate bounds every finite
stationary covariance sum. This is the finite version of the paper's
resolvent estimate and needs neither full support nor irreducibility.
TEXLINE: main.tex:982-1009 -/
theorem covariance_sum_le {π : FinDist Ω} {P : FinChain Ω}
    (hrev : Reversible π P) (hpsd : NonnegDefinite π P)
    (g : Ω → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hdual : ∀ H : Ω → ℝ, (ip π g H) ^ 2 ≤ C * dirichlet π P H H)
    (N : ℕ) :
    (∑ t ∈ Finset.range N, ip π g ((P.iter t).act g)) ≤ C := by
  let H : Ω → ℝ := fun x => ∑ t ∈ Finset.range N, (P.iter t).act g x
  have hsum : ip π g H = ∑ t ∈ Finset.range N, ip π g ((P.iter t).act g) := by
    simp only [ip, H, Finset.mul_sum]
    exact Finset.sum_comm
  have hnonneg : 0 ≤ ip π g H := by
    rw [hsum]
    exact Finset.sum_nonneg fun t _ => covariance_nonneg hrev hpsd g t
  have htail : 0 ≤ ip π H ((P.iter N).act g) := by
    have hexpand : ip π H ((P.iter N).act g) =
        ∑ t ∈ Finset.range N, ip π g ((P.iter (t + N)).act g) := by
      simp only [ip, H, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      change ip π ((P.iter t).act g) ((P.iter N).act g) = _
      rw [← ip_iter_transfer hrev, ← act_iter_add]
      rfl
    rw [hexpand]
    exact Finset.sum_nonneg fun t _ => covariance_nonneg hrev hpsd g (t + N)
  have henergy : dirichlet π P H H =
      ip π g H - ip π H ((P.iter N).act g) := by
    have ht := geometric_action_sub P g N
    change H - P.act H = g - (P.iter N).act g at ht
    calc
      _ = ip π H (H - P.act H) := by
        simp only [dirichlet, ip, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
      _ = ip π H (g - (P.iter N).act g) := by rw [ht]
      _ = _ := by
        change ip π H (fun x => g x - (P.iter N).act g x) = _
        rw [ip_comm π g H]
        simp only [ip, mul_sub, Finset.sum_sub_distrib]
  have hd := hdual H
  rw [henergy] at hd
  have hb : (ip π g H) ^ 2 ≤ C * ip π g H :=
    hd.trans (mul_le_mul_of_nonneg_left (by linarith) hC)
  rw [← hsum]
  nlinarith

end CountingMatroid.Analysis.StationaryCovarianceSum
