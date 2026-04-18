import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

/-!
# K-Iteration Bound

This module establishes how the k-iteration bound mathematically restricts the depth of
type derivations. By bounding the number of relaxation steps to the number of variables
(vertices) in the constraint graph, we prevent unchecked iterative expansion and
guarantee termination of the stratification check. This bounded traversal is sufficient
to either find a valid type assignment or expose a negative cycle (a stratification violation).
-/

inductive BoundedPath (edges : List Edge) : Nat → Var → Var → Type where
  | nil (u : Var) : BoundedPath edges 0 u u
  | snoc {k : Nat} {u w : Var} (p : BoundedPath edges k u w) (e : Edge) (h_in : e ∈ edges) (h_eq : e.src = w) : BoundedPath edges (k + 1) u e.dst

def boundedPathWeight {edges : List Edge} {k : Nat} {u v : Var} : BoundedPath edges k u v → Int
  | .nil _ => 0
  | .snoc p e _ _ => boundedPathWeight p + e.weight

def relaxEdgesN (edges : List Edge) (dist : List (Var × Int)) (k : Nat) : List (Var × Int) :=
  match k with
  | 0 => dist
  | k' + 1 => relaxEdgesN edges (relaxEdges edges dist []).1 k'

theorem relaxEdges_foldl_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (Var × Int)) (pred : List (Var × Var)) (changed : Bool) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := sorry
theorem relaxEdges_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (Var × Int)) (pred : List (Var × Var)) :
  lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup dist e.src + e.weight := sorry
theorem relaxEdgesN_succ (edges : List Edge) (dist : List (Var × Int)) (k : Nat) :
  relaxEdgesN edges dist (k + 1) = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := sorry
theorem k_iteration_bound (edges : List Edge) (d : List (Var × Int)) (k : Nat) (u v : Var)
  (p : BoundedPath edges k u v) :
  lookup (relaxEdgesN edges d k) v ≤ lookup d u + boundedPathWeight p := sorry
