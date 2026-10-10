import CountingMatroid.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

open Arlib.Computation

namespace CountingMatroid.Program
def cheatCasesOn (d : Roster Nat) : Nat :=
  Roster.casesOn (motive := fun _ => Nat) d (fun elems _ => elems.length)
end CountingMatroid.Program

/--
error: Seal breach in CountingMatroid.Program: [(CountingMatroid.Program.cheatCasesOn, Arlib.Computation.Roster.casesOn)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal CountingMatroid.Program
