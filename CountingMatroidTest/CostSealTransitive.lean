import CountingMatroid.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

open Arlib.Computation

namespace CountingMatroid.Program
def cheatTransitive (p : Charged StdOp Cell Nat) : Nat := Charged.steps (Rate.unit StdOp) p
end CountingMatroid.Program

/--
error: Seal breach in CountingMatroid.Program: [(CountingMatroid.Program.cheatTransitive, Arlib.Computation.Charged.steps)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal CountingMatroid.Program
