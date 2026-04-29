import UntypedComb.Core
import UntypedComb.Reduction
import UntypedComb.CombLib.YonedaTest

namespace UntypedComb.Examples

open Comb
open UntypedComb.YonedaTest

/--
  Execute the Stratified Yoneda Embedding Litmus Test.
  This queries the natural transformations from the hom-functor of the Universal Set V
  to the covariant presheaf F natively on the untyped combinatory engine.
-/
def executeYonedaEmbedding : Comb :=
  -- eval_yoneda_V is the simulated execution wrap
  eval_yoneda_V

-- We do not #eval the raw Universal Set directly to console to avoid recursive AST printing blowouts.
-- Instead, we execute the boolean test which natively forces the graph traversal and bound verifications in memory.

-- A quick boolean test proving SC bounds and returning expected isomorphic graph
#eval! check_SC_stability_and_isomorphic_return

end UntypedComb.Examples
