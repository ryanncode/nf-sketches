import UntypedComb.Core
import UntypedComb.CombLib.SelfModels
import UntypedComb.CombLib.Booleans

namespace UntypedComb.Examples

open Comb
open UntypedComb.CombLib.SelfModels
open UntypedComb.Booleans

/--
  Evaluate the Quine Atom.
  This models a set containing only an unreduced copy of itself.
  We test it against an identity function to ensure the engine correctly maps
  the self-referential graph loop using the U combinator prior to execution.
-/
def evaluateQuineAtom : Comb :=
  app I buildQuineAtom

#eval evaluateQuineAtom
#eval normalize evaluateQuineAtom

end UntypedComb.Examples
