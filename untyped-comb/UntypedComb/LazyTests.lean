import UntypedComb.Core
import UntypedComb.Reduction
import UntypedComb.MCM
import UntypedComb.DAG
import UntypedComb.CombLib.Recursion

namespace UntypedComb

-- 1. Create a negative-weight paradoxical cycle directly (V \in V).
-- Using the Y combinator to force self-application, creating infinite recursion.
def omega : Comb := Comb.app (Comb.app Comb.S Comb.I) Comb.I
def divergentTerm : Comb := Comb.app omega omega

-- 2. Mocking a negative cycle detection by assigning it an artificial graph state.
-- In reality, we'd compile the unstratified set theory sentence down.
def testGraph : DAG :=
  let c := divergentTerm
  (astToGraphAux c ⟨#[], #[]⟩).1

-- 3. We calculate the K-Iteration limit.
def testLimit : Nat := computeKIterationLimit testGraph

-- 4. Evaluate the divergent term using the bounding limits.
-- Without lazy thunks and K-Iteration boundaries, this would loop infinitely.
-- With K-Iteration limits, it halts and produces a terminal state.
def safeEvaluation : Comb :=
  -- If we detect it's a negative cycle (in our simple graph, it might not trigger < 0 without explicit edge weights)
  -- But we can force a low kLimit to demonstrate the halting.
  normalize divergentTerm 10 0

#eval safeEvaluation == Comb.terminal "K_ITERATION_HALT"

end UntypedComb
