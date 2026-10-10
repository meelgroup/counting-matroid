import CountingMatroid.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

open Arlib.Computation

namespace CountingMatroid.Program
def cheatMeasure (d : Roster Nat) : Charged StdOp Cell (Roster Nat) :=
  Charged.opUpdate (StdOp.roster .insert) (fun _ => Residency.ofFun fun _ => 0) id d
end CountingMatroid.Program

/--
error: Seal breach in CountingMatroid.Program: [(CountingMatroid.Program.cheatMeasure, Arlib.Computation.Charged.opUpdate), (CountingMatroid.Program.cheatMeasure, Arlib.Computation.Residency.ofFun)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal CountingMatroid.Program
