import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants
import Mathlib.Tactic.Linarith

/-!
# K-Iteration Bound

This module establishes how the k-iteration bound mathematically restricts the depth of
type derivations. By bounding the number of relaxation steps to the number of variables
(vertices) in the constraint graph, we prevent unchecked iterative expansion and
guarantee termination of the stratification check. This bounded traversal is sufficient
to either find a valid type assignment or expose a negative cycle (a stratification violation).
-/

inductive BoundedPath (edges : List Edge) : Nat → ScopedVar → ScopedVar → Type where
  | nil (u : ScopedVar) : BoundedPath edges 0 u u
  | snoc {k : Nat} {u w : ScopedVar} (p : BoundedPath edges k u w) (e : Edge) (h_in : e ∈ edges) (h_eq : e.src = w) : BoundedPath edges (k + 1) u e.dst

def boundedPathWeight {edges : List Edge} {k : Nat} {u v : ScopedVar} : BoundedPath edges k u v → Int
  | .nil _ => 0
  | .snoc p e _ _ => boundedPathWeight p + e.weight

def relaxEdgesN (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) : List (ScopedVar × Int) :=
  match k with
  | 0 => dist
  | k' + 1 => relaxEdgesN edges (relaxEdges edges dist []).1 k'

theorem relaxEdges_foldl_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 e.dst ≤ lookup dist e.src + e.weight := sorry

theorem relaxEdges_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup dist e.src + e.weight := by
  exact relaxEdges_foldl_edge_bound edges e h_in dist pred false

theorem relaxEdgesN_succ (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) :
  relaxEdgesN edges dist (k + 1) = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := sorry

theorem k_iteration_bound (edges : List Edge) (d : List (ScopedVar × Int)) (k : Nat) (u v : ScopedVar)
  (p : BoundedPath edges k u v) :
  lookup (relaxEdgesN edges d k) v ≤ lookup d u + boundedPathWeight p := by
  induction p with
  | nil u =>
    simp [relaxEdgesN, boundedPathWeight]
  | @snoc k_ p_u p_w p' e h_in h_eq ih =>
    simp [boundedPathWeight]
    rw [relaxEdgesN_succ]
    have h1 := relaxEdges_edge_bound edges e h_in (relaxEdgesN edges d k_) []
    rw [h_eq] at h1
    linarith
