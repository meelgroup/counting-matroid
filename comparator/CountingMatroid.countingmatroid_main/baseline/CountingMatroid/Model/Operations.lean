import Arlib.Computation.Charged
import Arlib.Computation.Machine
import CountingMatroid.Model.Prelude

set_option autoImplicit false

/-!
# Primitive work currency for the oracle algorithm

Correspondence ledger: main.tex:69–83 charges calls to the two supplied
independence oracles separately from other bit operations. `Op.oracleFirst` and
`Op.oracleSecond` mark those calls. `Op.word` names one Arlib RAM instruction;
`Op.fairBit` marks one read of an independent unbiased input bit. The paper's
bit-cost convention is unspecified: the word width, multiword arithmetic,
query construction, memory allocation, and rational encoding still require
concrete RAM code and realization proofs. A `Charged` tally alone is not such a
proof. No composite annealing or pretest action is an operation here.
-/

namespace CountingMatroid.Model.Operations

open CountingMatroid.Model

/-- Distinct primitive charges. An oracle call is never counted as an ordinary
RAM operation; constructing its n-bit argument must separately pay for RAM work. -/
inductive Op where
  | oracleFirst
  | oracleSecond
  | fairBit
  | word (instruction : Arlib.Computation.Op)
  deriving DecidableEq

/-- One storage kind for the abstract charged authoring layer. Physical RAM
capacity and cell ownership need separate realization proofs. -/
inductive Cell where
  | cell
  deriving DecidableEq

/-- A positive price table. The rate remains explicit; in particular it makes
no unproved constant-time claim for arbitrary-precision rationals. -/
def rate (oraclePrice wordPrice bitPrice : ℕ)
    (hOracle : 0 < oraclePrice) (hWord : 0 < wordPrice)
    (hBit : 0 < bitPrice) : Arlib.Computation.Rate Op where
  cost
    | .oracleFirst | .oracleSecond => oraclePrice
    | .fairBit => bitPrice
    | .word _ => wordPrice
  one_le := by
    intro op
    cases op <;> simp [hOracle, hWord, hBit, Nat.one_le_iff_ne_zero,
      Nat.ne_of_gt]

/-- A supplied exact independence oracle queried once. `which` distinguishes
the two original oracles in the cost vector. -/
def oracleQuery {n : ℕ} (which : Bool) (oracle : (Fin n → Bool) → Bool)
    (query : Fin n → Bool) : Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op
    (if which then Op.oracleSecond else Op.oracleFirst) (oracle query)

/-- Compare the represented input size with zero. Its single-word realization
requires a word wide enough for the input-size encoding. -/
def inputSizeIsZero (n : ℕ) : Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op (Op.word .eq) (n == 0)

/-- A single fair-bit read. The tape is supplied independently of problem input;
its fair product law belongs in `Model.Run`, not in this deterministic wrapper. -/
def fairBit {ι : Type} (tape : ι → Bool) (site : ι) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op Op.fairBit (tape site)

/-- Add one element to the represented subset. The present charged currency
records a word step; a concrete representation and its bit cost are still owed. -/
def insertElement {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    Arlib.Computation.Charged Op Cell (Finset (Fin n)) :=
  Arlib.Computation.Charged.op (Op.word .store) (insert i s)

/-- Materialize an n-bit oracle query. The quadratic tally allows a simple
linear scan of the set for each bit; the corresponding RAM code is unresolved. -/
def encodeQuery {n : ℕ} (s : Finset (Fin n)) :
    Arlib.Computation.Charged Op Cell (Fin n → Bool) :=
  Arlib.Computation.Charged.opMany (Op.word .load) (n * (n + 1))
    (fun i => decide (i ∈ s))

/-- One successor and one Boolean branch test used by bounded counters. -/
def successor (i : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .add) (i + 1)

def lessThan (i j : ℕ) : Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op (Op.word .lt) (i < j)

/-- Membership in an n-element represented subset, charged for a linear scan. -/
def containsElement {n : ℕ} (s : Finset (Fin n)) (i : Fin n) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.opMany (Op.word .load) (n + 1) (decide (i ∈ s))

/-- Membership in a paired 2n-element represented subset. -/
def containsPaired {n : ℕ} (s : Finset (Fin n × Bool)) (i : Fin n × Bool) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.opMany (Op.word .load) (2 * n + 1) (decide (i ∈ s))

def erasePaired {n : ℕ} (s : Finset (Fin n × Bool)) (i : Fin n × Bool) :
    Arlib.Computation.Charged Op Cell (Finset (Fin n × Bool)) :=
  Arlib.Computation.Charged.opMany (Op.word .store) (2 * n + 1) (s.erase i)

def insertPaired {n : ℕ} (s : Finset (Fin n × Bool)) (i : Fin n × Bool) :
    Arlib.Computation.Charged Op Cell (Finset (Fin n × Bool)) :=
  Arlib.Computation.Charged.opMany (Op.word .store) (2 * n + 1) (insert i s)

def natEqual (a b : ℕ) : Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op (Op.word .eq) (a == b)

def indexEqual {n : ℕ} (a b : Fin n) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op (Op.word .eq) (a == b)

def natAdd (a b : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .add) (a + b)

def natSub (a b : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .sub) (a - b)

def natMul (a b : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .mul) (a * b)

/-- Number of bits needed for a uniform integer below `v`, for `v > 1`. -/
def uniformWidth (v : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .clz) ((v - 1).log2 + 1)

/-- Append a read fair bit to the current rejection-trial integer. -/
def appendBit (acc : ℕ) (bit : Bool) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .shl) (2 * acc + if bit then 1 else 0)

def isSome {α : Type} (value : Option α) :
    Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.op (Op.word .eq) value.isSome

/-- Elementary rational pair arithmetic, charged by a quadratic function of
the operand encodings. The required RAM realization is not in this pin. -/
private def rationalSize (q : ℚ) : ℕ :=
  q.num.natAbs.log2 + q.den.log2 + 3

def ratAdd (a b : ℚ) : Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.opMany (Op.word .add)
    ((rationalSize a + rationalSize b) ^ 2) (a + b)

def ratSub (a b : ℚ) : Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.opMany (Op.word .sub)
    ((rationalSize a + rationalSize b) ^ 2) (a - b)

def ratMul (a b : ℚ) : Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.opMany (Op.word .mul)
    ((rationalSize a + rationalSize b) ^ 2) (a * b)

def ratDiv (a b : ℚ) : Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.opMany (Op.word .udiv)
    ((rationalSize a + rationalSize b) ^ 2) (a / b)

def ratLess (a b : ℚ) : Arlib.Computation.Charged Op Cell Bool :=
  Arlib.Computation.Charged.opMany (Op.word .lt)
    (rationalSize a + rationalSize b) (decide (a < b))

def ratOfNat (a : ℕ) : Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.opMany (Op.word .store) (a.log2 + 1) (a : ℚ)

def rationalCeil (a : ℚ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.opMany (Op.word .udiv)
    ((rationalSize a) ^ 2) (Int.toNat a.ceil)

/-- A word-length upper bound for the bounded searches in the schedule. -/
def binaryLoopBound (a : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .clz) (a.log2 + 8)

/-- Logical table access and update; the corresponding represented storage,
address arithmetic and frame proof are outstanding RAM obligations. -/
def multiplierRead {n : ℕ} (w : Multipliers n) (i : DefectIndex n) :
    Arlib.Computation.Charged Op Cell ℚ :=
  Arlib.Computation.Charged.opMany (Op.word .load) (n * n + 1) (w i)

def multiplierWrite {n : ℕ} (w : Multipliers n) (i : DefectIndex n) (v : ℚ) :
    Arlib.Computation.Charged Op Cell (Multipliers n) :=
  Arlib.Computation.Charged.opMany (Op.word .store) (n * n + 1)
    (fun j => if j = i then v else w j)

def learnedWeightRead {n : ℕ} (tables : LearnedWeights n) (phase L : ℕ) :
    Arlib.Computation.Charged Op Cell (Multipliers n) :=
  Arlib.Computation.Charged.opMany (Op.word .load) (L * n * n + 1)
    (tables phase)

def learnedWeightWrite {n : ℕ} (tables : LearnedWeights n) (phase L : ℕ)
    (weights : Multipliers n) :
    Arlib.Computation.Charged Op Cell (LearnedWeights n) :=
  Arlib.Computation.Charged.opMany (Op.word .store) (L * n * n + 1)
    (fun k => if k = phase then weights else tables k)

def countRead {n : ℕ} (counts : StateKind n → ℕ) (kind : StateKind n) :
    Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.opMany (Op.word .load) (n * n + 2) (counts kind)

def countIncrement {n : ℕ} (counts : StateKind n → ℕ) (kind : StateKind n) :
    Arlib.Computation.Charged Op Cell (StateKind n → ℕ) :=
  Arlib.Computation.Charged.opMany (Op.word .store) (3 * (n * n + 2))
    (fun k => if k = kind then counts k + 1 else counts k)

def allocateCounts (n : ℕ) :
    Arlib.Computation.Charged Op Cell (StateKind n → ℕ) :=
  Arlib.Computation.Charged.opMany (Op.word .alloc) (n * n + 1)
    (fun _ => 0)

def initialWeights (n : ℕ) :
    Arlib.Computation.Charged Op Cell (Multipliers n) :=
  Arlib.Computation.Charged.opMany (Op.word .alloc) (n * n + 1)
    (fun _ => 4)

def allocateLearnedWeights (n L : ℕ) (initial : Multipliers n) :
    Arlib.Computation.Charged Op Cell (LearnedWeights n) :=
  Arlib.Computation.Charged.opMany (Op.word .alloc) (L * (n * n + 1))
    (fun _ => initial)

def rationalNumerator (q : ℚ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.opMany (Op.word .load) (rationalSize q) q.num.natAbs

def rationalDenominator (q : ℚ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.opMany (Op.word .load) (rationalSize q) q.den

def consRational (q : ℚ) (values : List ℚ) :
    Arlib.Computation.Charged Op Cell (List ℚ) :=
  Arlib.Computation.Charged.op (Op.word .store) (q :: values)

def reverseRationals (values : List ℚ) :
    Arlib.Computation.Charged Op Cell (List ℚ) :=
  Arlib.Computation.Charged.opMany (Op.word .load)
    (values.length + 1) values.reverse

def nthRational (values : List ℚ) (k : ℕ) :
    Arlib.Computation.Charged Op Cell (Option ℚ) :=
  Arlib.Computation.Charged.opMany (Op.word .load)
    (values.length + 1) (values[k]?)

def halfNat (k : ℕ) : Arlib.Computation.Charged Op Cell ℕ :=
  Arlib.Computation.Charged.op (Op.word .udiv) (k / 2)

end CountingMatroid.Model.Operations
