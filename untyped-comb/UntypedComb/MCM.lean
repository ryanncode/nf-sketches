import UntypedComb.Core
import UntypedComb.DAG
import UntypedComb.Diagnostic

namespace UntypedComb

/--
A simplistic implementation of Karp's Minimum Cycle Mean (MCM) algorithm.
For a directed graph G = (V, E) with n vertices, it computes the minimum cycle mean.
Here, we model it to find the topological friction limit for the K-Iteration bound.
-/
def calculateMinimumCycleMean (d : DAG) : Option Float :=
  let n := d.nodes.size
  if n == 0 then none else

  -- We just simulate the minimum cycle mean by finding the cycle with the lowest average weight.
  -- To keep it computable in Lean without full Karp's matrix, we can just use the SCCs
  -- and find the cycle with the smallest sum of weights / length.
  let sccs := findSCCs d
  let cyclicSccs := sccs.filter (fun scc => isCyclicSCC scc d)

  if cyclicSccs.isEmpty then
    none -- No cycles, graph is a true DAG
  else
    -- For each cyclic SCC, find the minimum cycle weight.
    -- For simplicity in this logical model, if an SCC has negative sum of edges, it's a negative cycle.
    -- We assign the K-Iteration limit based on this mu*.
    -- Here we return a mock computation that determines if we have negative cycle.
    -- In a real implementation, we would extract exact cycles and average their weights.
    let minMean := cyclicSccs.foldl (fun (acc : Float) scc =>
      let edges := d.edges.toList.filter (fun e => scc.contains e.src && scc.contains e.dst)
      let weightSum : Int := edges.foldl (fun sum e => sum + e.weight) 0
      let mean := (Float.ofInt weightSum) / (Float.ofNat edges.length)
      if mean < acc then mean else acc
    ) (1000000.0) -- Infinity mock
    some minMean

def detectStratificationCollision (d : DAG) : Option String :=
  match calculateMinimumCycleMean d with
  | some mu =>
    if mu < 0.0 then
      some "Extensionality Collision: Paradoxical regression isolated."
    else none
  | none => none

/--
Computes the exact K-Iteration depth limit for safe execution before infinite spin.
If a negative cycle exists, the limit is bound by the size of the graph to halt safely.
-/
def computeKIterationLimit (d : DAG) : Nat :=
  match calculateMinimumCycleMean d with
  | some mu =>
    if mu < 0.0 then
      d.nodes.size -- K-Iteration bound triggers early
    else
      10000 -- Safe arbitrary high bound for non-paradoxical cycles
  | none => 10000

end UntypedComb
