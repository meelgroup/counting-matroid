/-
The program's forbidden internals and sanctioned operation vocabulary.

Everything this development takes on trust about where its algorithm ends is
here. Keep both lists short and treat growth as a finding rather than as a
build fix.
-/
import Lean
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Std

open Lean

namespace CountingMatroid.Meta

/-- Constants an algorithm may not mention.  The first six are the eliminators
the compiler generates public; the rest would let a program read a dictionary,
take a computation's value, or re-price its own tally. -/
def forbiddenInProgram : List Name :=
  [``Arlib.Computation.Roster.casesOn, ``Arlib.Computation.Roster.rec,
   ``Arlib.Computation.Roster.recOn, ``Arlib.Computation.Charged.casesOn,
   ``Arlib.Computation.Charged.rec, ``Arlib.Computation.Charged.recOn,
   ``Arlib.Computation.Roster.toFinset, ``Arlib.Computation.Roster.card,
   ``Arlib.Computation.Roster.ofFinset, ``Arlib.Computation.Charged.val,
   ``Arlib.Computation.Charged.exchange,
   -- **Observing a computation is reading its data.**  `Roster.cost_filterErase`
   -- equates a thinning pass's tally to `d.card`, so `(filterErase …).cost coin`
   -- is a computable, free cardinality and `pure (decide (… = thr))` is a
   -- zero-cost `cardEq`.  Reading a cost "produces no value" only until `decide`
   -- is applied to it.
   --
   -- `Charged.steps` is deliberately **not** listed, and that is the test of the
   -- scan below rather than an oversight: it is `CostVec.steps C p.cost` one hop
   -- away, so the transitive walk finds it, and a planted breach confirms that
   -- it is rejected with the list in exactly this state.  Anything else built on
   -- `cost` is caught the same way, without anyone having to think of it first.
   ``Arlib.Computation.Charged.cost,
   -- **the space half.**  `Charged.space`, `Profile.net`/`peak` and
   -- `Residency.at'` are noncomputable, so the compiler already rejects a
   -- program that reads one; they are listed anyway so that a `noncomputable
   -- def` cannot silence it, which is the same standing `Roster.card` has.
   ``Arlib.Computation.Charged.space, ``Arlib.Computation.Profile.net,
   ``Arlib.Computation.Profile.peak, ``Arlib.Computation.Residency.at',
   -- and the two that would let an algorithm re-price what it holds.  An author
   -- who can call `opUpdate` supplies their own measure, and a measure that
   -- reports nothing makes every structure free — `Charged.exchange (fun _ => 0)`
   -- for space.  A program calls `Roster.insert`, which passes a private measure.
   ``Arlib.Computation.Charged.opUpdate, ``Arlib.Computation.Residency.ofFun,
   ``Arlib.Computation.Profile.between,
   -- and the two classes that *name* what an operation touches.  Neither can make
   -- a dictionary free — arlib fixes one cell per element and one charge per
   -- operation — but a rival `RosterCells` can attribute cells to a kind nobody is
   -- bounding, and a rival `RosterOps` files charges under a name nobody is
   -- counting.  Declaring an instance is the development's business, done once
   -- beside the currency; doing it inside a line of the algorithm is not.
   ``Arlib.Computation.RosterCells.mk, ``Arlib.Computation.RosterOps.mk,
   -- the computable test accessors.  They exist so that `#guard` can read a
   -- measured peak and compare it against the proved bound — the protocol's CI
   -- check 6, which is the one check that catches an accounting that is wrong
   -- but internally consistent.  A test lives outside this namespace; an
   -- algorithm that read one would have a free size query.
   ``Arlib.Computation.Charged.peakAt, ``Arlib.Computation.Charged.netAt,
   ``Arlib.Computation.Profile.peakAt, ``Arlib.Computation.Profile.netAt,
   -- **the randomness and the answer register.**  A bare `bits : Fin n → Bool`
   -- is a free oracle and a bare `level : ℕ` is a free read; sealing them is what
   -- turned `acceptsAt level bits` and `|X| * 2 ^ level` from computations the
   -- program did for nothing into operations it performs.  All four views are
   -- noncomputable, so the compiler already rejects a program that reads one;
   -- listing them means a `noncomputable def` cannot silence it.
   ``Arlib.Computation.Block.get, ``Arlib.Computation.Coins.heads',
   ``Arlib.Computation.Sampler.levelOf, ``Arlib.Computation.Slot.get,
   -- and the boundaries that *build* them.  A program that could seal its own
   -- block could choose the bits, which is worse than reading them.
   ``Arlib.Computation.Block.ofFun, ``Arlib.Computation.Coins.ofFinset,
   ``Arlib.Computation.Slot.ofOption,
   -- the naming instances, on the footing `RosterOps.mk` is on
   ``Arlib.Computation.RandOps.mk, ``Arlib.Computation.SlotOps.mk,
   -- and the eliminators the compiler generates public for the four new
   -- sealed carriers
   ``Arlib.Computation.Block.casesOn, ``Arlib.Computation.Block.rec,
   ``Arlib.Computation.Block.recOn,
   ``Arlib.Computation.Coins.casesOn, ``Arlib.Computation.Coins.rec,
   ``Arlib.Computation.Coins.recOn,
   ``Arlib.Computation.Sampler.casesOn, ``Arlib.Computation.Sampler.rec,
   ``Arlib.Computation.Sampler.recOn,
   ``Arlib.Computation.Slot.casesOn, ``Arlib.Computation.Slot.rec,
   ``Arlib.Computation.Slot.recOn,
   -- **and `Charged.op` itself, except behind audited operation wrappers.**
   --
   -- `Charged.op o a` is arlib's escape hatch: one operation of the currency,
   -- returning a value the algorithm computed for itself.  It is the primitive
   -- for project-local operations when a development touches something arlib
   -- has not sealed, but the operation belongs in `Model/Operations.lean`, not
   -- inline in the program.
   --
   -- What it costs to leave open is not a wrong number but an unwatched one.
   -- `Charged.op (StdOp.rand .accept) (acceptsAt level bits)` charged one operation for an
   -- `O(level)` scan of a bare bit block, and read a bare level to do it; the
   -- test `Charged.op (StdOp.slot .test) answer.isNone` read an ordinary field, so
   -- only the inspections its author chose to write down were ever charged.
   -- Both are gone: the randomness is a `Block` and a `Coins`, the level is
   -- inside a `Sampler`, the answer is a `Slot`, and every question the
   -- algorithm asks of any of them is an operation whose price is fixed in
   -- arlib.
   --
   -- So this entry is a claim about the algorithm, checked: **every line of the
   -- paper's pseudocode is either a standard operation of the library or a
   -- project-local primitive named in `Model/Operations.lean`.** If a future
   -- line genuinely is not in either vocabulary, the honest fix is to expose
   -- that operation in the cost model — not to delete this entry.
   ``Arlib.Computation.Charged.op, ``Arlib.Computation.Charged.opMany]

/-- **The frontier the transitive walk stops at: the vocabulary an algorithm is
allowed to speak.**

A transitive scan without a frontier walks into the implementation of everything
it permits, and then rejects it.  `Roster.filterErase` is built from `Roster.erase`,
which is built from `Charged.opUpdate` — which an *algorithm* may not call, and
which is exactly what a dictionary operation is made of.  Without this list the
seal rejects `Program.thin`, the thinning line of the paper's own algorithm.

So the walk stops here, and what that means is: **the internals of these
operations are not this development's to audit.**  They are arlib's, and
`arlib/scripts/ComputationAudit.lean` audits them — over 511 declarations, with
its own `areaByPermission` naming `Roster.erase` and `Roster.insert` as the two
declarations entitled to call `opUpdate`, and with the private `Roster.slots` as
the only measure they can pass.  The two audits compose: this one says the
algorithm speaks only the sanctioned vocabulary, and that one says the vocabulary
is honest.

If this grows past the operations a paper's pseudocode actually names, something
is being exempted rather than checked. -/
def sanctioned : List Name :=
  [-- **the development's own two tables.**  `RosterCells.mk` and `RosterOps.mk` are
   -- forbidden above, and every dictionary operation reaches the instances that
   -- build them, so without these two entries the walk rejects `Program.thin` —
   -- the thinning line of the paper's own algorithm — for the crime of using a
   -- dictionary.  Stopping here says: *using* a dictionary is not *re-declaring*
   -- what one costs.  A program that declares its own rival instance mentions
   -- `RosterOps.mk` directly and is caught; one that uses a rival instance is
   -- caught too, because that instance is not on this list and the walk goes on
   -- into it.  What is exempted is these two declarations, by name — six lines
   -- sitting beside the currency they name, and the most-read lines in `Model/`.
   ``Arlib.Computation.stdRosterCells, ``Arlib.Computation.stdRosterOps,
   ``Arlib.Computation.stdRandOps, ``Arlib.Computation.stdSlotOps,
   ``Arlib.Computation.Roster.erase, ``Arlib.Computation.Roster.insert,
   ``Arlib.Computation.Roster.cardEq, ``Arlib.Computation.Roster.size,
   ``Arlib.Computation.Roster.mem, ``Arlib.Computation.Roster.filterErase,
   ``Arlib.Computation.Roster.empty,
   ``Arlib.Computation.Coins.flip, ``Arlib.Computation.Sampler.accept,
   ``Arlib.Computation.Sampler.halve, ``Arlib.Computation.Sampler.inflate,
   ``Arlib.Computation.Sampler.start,
   ``Arlib.Computation.Slot.isEmpty, ``Arlib.Computation.Slot.fill,
   ``Arlib.Computation.Slot.empty,
   ``Arlib.Computation.Charged.pure, ``Arlib.Computation.Charged.bind,
   ``Arlib.Computation.Charged.foldl]

/-- Project-local primitive wrappers.  These are not arlib internals, but they
are part of the audit surface: `Model/Operations.lean` names the currency the
paper counts in, and `Prior` or `Analysis/` supplies the certificates behind
its rates.  Stopping at this namespace lets a program call those named
primitives while still rejecting hand-priced `Charged.op` directly in
`Program.lean`. -/
def sanctionedPrefixes : List Name :=
  [`CountingMatroid.Model.Operations]

end CountingMatroid.Meta

/-
Machine-checks that the cost of the development is the cost of the algorithm.

Two checks, run as commands so that they fire on every build rather than in a
script somebody has to remember, and placed here rather than beside the
algorithm because they are tooling — the same reason `ModelClosure` lives here,
and, like it, deliberately *outside* the surface they check.

## What the compiler already does

`Arlib.Computation.Charged` has a private constructor, so a program's tally is a
function of its text: `pure` is free, `bind` adds, `Charged.op` charges one.
`Charged.val` and the sealed carriers' views are noncomputable, so a program
cannot read a value or a dictionary without a charged operation. Most of the
seal is therefore the elaborator's, and needs nothing here.

## What it additionally checks

 **Inside the algorithm** two routes stay open. A structure's `casesOn` is
generated public even when its constructor is private, so a determined author
can project the private field out; and `noncomputable def` silences the error
 that stops a program reading a dictionary. `#programSeal` closes both.
 -/
open Lean Elab Command

namespace CountingMatroid.Meta

/-- INTERNAL: is `c`'s type a `Prop`?  Recursion stops there — a theorem's proof
cannot compute anything, so what it mentions is not work a program performs. -/
private def isPropConst (c : Name) : CommandElabM Bool := do
  match (← getEnv).find? c with
  | some ci => liftTermElabM (Lean.Meta.isProp ci.type)
  | none => return true

/-- **Does `c` reach one of `targets`?**

The scan has to be transitive, and this is not a refinement.  `#programSeal` used
to read `ci.value?.getUsedConstants` — a declaration's *direct* constants — and
that is a spelling test, not a seal.  `Charged.steps` is `CostVec.steps C p.cost`
one hop away in arlib, so a program that calls it mentions `Charged.cost`
nowhere the check can see, and the free-`cardEq` cheat goes through against a
blacklist that names `cost`.

`memo` is threaded so the reachable subgraph is walked once for the whole
namespace rather than once per declaration; a constant is memoised as `false`
before its own successors are explored, which is what stops the recursion on the
cycles that mutual definitions create. -/
private partial def reaches (targets : List Name) (memo : Std.HashMap Name Bool)
    (c : Name) : CommandElabM (Bool × Std.HashMap Name Bool) := do
  if let some b := memo[c]? then return (b, memo)
  if targets.contains c then return (true, memo.insert c true)
  -- the frontier: an algorithm may call these, and what they are made of is
  -- arlib's audit's business, or the project-local operation model's business,
  -- not this program scan's.
  if sanctioned.contains c || sanctionedPrefixes.any (fun p => p.isPrefixOf c) then
    return (false, memo.insert c false)
  let mut m := memo.insert c false
  let mut hit := false
  if !(← isPropConst c) then
    if let some ci := (← getEnv).find? c then
      if let some v := ci.value? then
        for u in v.getUsedConstants do
          if !hit then
            let (h, m') ← reaches targets m u
            m := m'
            hit := h
  return (hit, m.insert c hit)

/-- **The algorithm may not read for free.**  Checks every non-`Prop`
declaration under the given namespace: none may be `noncomputable`, and none may
mention `forbiddenInProgram`. -/
elab "#programSeal " id:ident : command => do
  let ns := id.getId
  let canonical := `CountingMatroid.Program
  unless ns == canonical do
    throwError m!"Program seal must target the canonical namespace {canonical}, not {ns}."
  let env ← getEnv
  let mut bad : Array (Name × Name) := #[]
  let mut count : Nat := 0
  let mut memo : Std.HashMap Name Bool := {}
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    unless ns.isPrefixOf c do continue
    if ← liftTermElabM (Lean.Meta.isProp ci.type) then continue
    count := count + 1
    if Lean.isNoncomputable env c then bad := bad.push (c, `noncomputableProgram)
    match ci.value? with
    | some v =>
        for u in v.getUsedConstants do
          if forbiddenInProgram.contains u then
            -- a direct use: name the forbidden constant, which is the useful message
            bad := bad.push (c, u)
          else
            -- an indirect use: name the intermediary the program actually called,
            -- since that is what its author has to stop calling
            let (hit, memo') ← reaches forbiddenInProgram memo u
            memo := memo'
            if hit then bad := bad.push (c, u)
    | none => pure ()
  if count == 0 then
    throwError m!"Program seal checked zero declarations under {ns}.  Put the executable       declarations from Model/Program.lean in this exact namespace; a vacuous seal is not a seal."
  unless bad.isEmpty do
    throwError m!"Seal breach in {ns}: {bad.toList}.  A program that reads a \
      dictionary without a charged operation, or that is marked noncomputable, \
      can perform work it does not pay for."
  logInfo m!"Program seal: {count} declarations under {ns}, none noncomputable, \
    none reaching a free read of a dictionary or of a computation's own tally \
    (transitively, through {memo.size} constants)."

/-- **Everything in the algorithm's module computes.**

Checks every author-written declaration *defined in a module under `mod`*: none
may be `noncomputable`, and none may be a specification — a `def` whose result is
a `Prop`, or a `Set`, which is a `Prop`-valued function wearing other clothes.
Theorems are skipped: a proof obligation such as a `Fintype` witness's
exhaustiveness lemma is part of writing the program down, and a proof computes
nothing in any case.

**Why this is not `#programSeal` again.**  `#programSeal` guards the canonical
declaration namespace. This guards the *file*, which is the unit a reader opens,
and also rejects executable declarations in that file that were placed outside
the canonical namespace.

**Why "computes" is the right test for "is part of the program".**  It is not a
proxy.  A `noncomputable def` is precisely a definition Lean cannot run, and it is
also the one route past the compiler's half of the cost seal — `Roster.card` and
`Charged.val` are noncomputable, so a program that reads one is rejected unless
its author writes `noncomputable`, at which point the elaborator falls silent.
Rejecting the keyword outright in the algorithm's module closes that door and
answers the reader's question at the same time.  The `Prop` half catches what the
compiler has no opinion on: `PaperItemSpaceBigO` is a perfectly computable
`def … : Prop`, and it is the paper's asymptotic sentence, not a line of the
algorithm. -/
elab "#executableModule " mod:ident : command => do
  let prefix_ := mod.getId
  let programNs := `CountingMatroid.Program
  let env ← getEnv
  let mut bad : Array (Name × String) := #[]
  let mut count : Nat := 0
  for (c, ci) in env.constants.toList do
    if c.isInternal then continue
    unless (`CountingMatroid).isPrefixOf c do continue
    -- `getModuleIdxFor?` returns none for the module being elaborated right now,
    -- which is exactly the one this check is invoked in
    match env.getModuleIdxFor? c with
    | some idx =>
        unless prefix_.isPrefixOf ((env.allImportedModuleNames[idx.toNat]?).getD `«unknown») do
          continue
    | none => unless prefix_.isPrefixOf env.mainModule do continue
    -- a theorem is not a program; see the docstring
    if ci.isTheorem then continue
    if ← liftTermElabM (Lean.Meta.isProp ci.type) then continue
    count := count + 1
    unless programNs.isPrefixOf c do
      bad := bad.push (c, s!"outside canonical program namespace {programNs}")
    if Lean.isNoncomputable env c then bad := bad.push (c, "noncomputable")
    -- a definition whose result is a `Prop` is a specification.  The telescope
    -- reduces as it goes, so `Set α` is seen through to `α → Prop` — a `Set` is
    -- a specification wearing other clothes, and `accurateEvent` was one
    if ← liftTermElabM (Lean.Meta.forallTelescopeReducing ci.type fun _ body => do
        return (← Lean.Meta.whnf body).isProp) then
      bad := bad.push (c, "specification, not a program")
  unless bad.isEmpty do
    throwError m!"Not executable in {prefix_}: {bad.toList}.  This module is the \
      algorithm; a definition that cannot be run is not part of it, and \
      `noncomputable` is also the one route past the compiler's half of the cost \
      seal.  Move it to `Model/Run.lean` (the randomised run) or \
      `Model/Prelude.lean` (the vocabulary the theorems are stated in)."
  logInfo m!"Executable: {count} definitions in {prefix_}, none noncomputable, \
    none a specification."

end CountingMatroid.Meta
