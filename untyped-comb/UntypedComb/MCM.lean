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
  
  let inf := 1000000.0
  let negInf := -1000000.0
  
  let incomingEdges := (List.range n).map (fun v =>
    d.edges.toList.filter (fun e => e.dst.id == v)
  )
  
  let stepF (f_prev : List Float) : List Float :=
    (List.range n).map (fun v =>
      let edges_v := incomingEdges.getD v []
      edges_v.foldl (fun acc e =>
        let u_val := f_prev.getD e.src.id inf
        if u_val != inf then
          let val := u_val + Float.ofInt e.weight
          if val < acc then val else acc
        else acc
      ) inf
    )
    
  let f0 := List.replicate n 0.0
  let rec buildF (k : Nat) (f_prev : List Float) (acc : List (List Float)) : List (List Float) :=
    match k with
    | 0 => acc.reverse
    | k' + 1 =>
      let f_next := stepF f_prev
      buildF k' f_next (f_next :: acc)
      
  let fk_matrix := buildF n f0 [f0]
  
  let fn_row := fk_matrix.getD n []
  
  let maxVals := (List.range n).map (fun v =>
    if fn_row.getD v inf == inf then negInf
    else
      let vals := (List.range n).map (fun k =>
        let fk_row := fk_matrix.getD k []
        let fkv := fk_row.getD v inf
        if fkv == inf then negInf
        else (fn_row.getD v inf - fkv) / (Float.ofNat (n - k))
      )
      vals.foldl (fun a b => if a > b then a else b) negInf
  )
  
  let lambda_star := maxVals.foldl (fun a b => if a < b then a else b) inf
  
  if lambda_star == inf then none else some lambda_star

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
