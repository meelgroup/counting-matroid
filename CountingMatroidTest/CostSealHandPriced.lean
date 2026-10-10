import CountingMatroid.Meta.CostSeal
import Arlib.Computation.Charged
import Arlib.Computation.Roster
import Arlib.Computation.Rand
import Arlib.Computation.Slot
import Arlib.Computation.Std

open Arlib.Computation

namespace CountingMatroid.Program
-- The original wrote this against the development's own `BitBlock` and
-- `acceptsAt`, which is the shape the algorithm actually had. Here it is a
-- bare function on `Nat`, so that the breach library builds with nothing but
-- arlib and can be a default target from the first commit of a project. The
-- property under test is unchanged: the charge says one coin, and the seal
-- cannot see what the argument cost.
def cheatHandPriced (level : Nat) (bits : Nat → Bool) : Charged StdOp Cell Bool :=
  Charged.op (StdOp.rand .accept) (bits level)
end CountingMatroid.Program

/--
error: Seal breach in CountingMatroid.Program: [(CountingMatroid.Program.cheatHandPriced, Arlib.Computation.Charged.op)].  A program that reads a dictionary without a charged operation, or that is marked noncomputable, can perform work it does not pay for.
-/
#guard_msgs (whitespace := lax) in
#programSeal CountingMatroid.Program
