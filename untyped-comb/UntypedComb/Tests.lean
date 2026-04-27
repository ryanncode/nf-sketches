import UntypedComb.Core
import UntypedComb.Topological
import UntypedComb.Diagnostic

namespace UntypedComb

/--
Unit test: The un-T-weaked K combinator fails topological bounds checking.
This physically replicates the exact normalization breakdown mapped in seq-embed.
-/
def test_k_combinator_failure : Bool :=
  match reduceCutCombinator Comb.K with
  | EvaluationResult.ExtensionalityCollision _ => true
  | _ => false

/--
Unit test: A term that has been properly stabilized using the T-operator
successfully navigates the extensionality bound checks.
This represents TA -> (B -> A).
-/
def test_t_weaked_term_success : Bool :=
  -- Simulating a basic term that resolves to a shifted level.
  let stabilizedTerm := injectTWeaking Comb.I 1 0
  match reduceCutCombinator stabilizedTerm with
  | EvaluationResult.Normalized _ => true
  | _ => false

#eval test_k_combinator_failure
#eval test_t_weaked_term_success

end UntypedComb
