import UntypedComb.Core
import UntypedComb.DAG
import UntypedComb.Reduction

namespace UntypedComb

-- Test: AST to DAG Translation Length
def testTranslationSize : Bool :=
  let c := Comb.app Comb.K Comb.I
  let d := toGraph c
  d.nodes.size == 3 && d.edges.size == 2

#eval testTranslationSize

-- Test: Identify trivial SCC in flat graph (should just be single nodes)
def testSCCFlat : Bool :=
  let c := Comb.app Comb.K Comb.I
  let d := toGraph c
  let sccs := findSCCs d
  sccs.length == 3 -- 3 separate nodes, no cycles

#eval testSCCFlat

-- Test: Cyclic DAG projection (conceptually represented here as self-referential compile)
def testAcyclicCompile : Bool :=
  let omega := Comb.app (Comb.var "x") (Comb.var "x")
  let compiled := compileAcyclic omega
  match compiled with
  | Comb.app (Comb.var "x") (Comb.var "x") => true
  | _ => false

#eval testAcyclicCompile

end UntypedComb
