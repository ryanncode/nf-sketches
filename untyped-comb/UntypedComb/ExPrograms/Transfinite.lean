import UntypedComb.Core
import UntypedComb.CombLib.Cardinals

namespace UntypedComb.Examples

open Comb
open UntypedComb.CombLib.Cardinals

/--
  Execute Cardinal Addition: |A| + |B| = |A ∪ B|.
  The engine mechanically synthesizes Thomas Forster's T-operator (x ↦ ι"x) on-the-fly,
  shifting the relative integer weights of the variables to ensure the S and K
  reductions remain completely type-safe through self-regulation.
-/
def addAlephNulls : Comb :=
  cardAdd aleph0 aleph0

#eval addAlephNulls
#eval normalize addAlephNulls

end UntypedComb.Examples
