import Mathlib.Data.Fintype.Basic

/-!
# Finite Type Graphs for Combinatorial Proofs

This module defines the graph structures over finite types (`Fintype`).
The shift to finite types is a deliberate design choice to unlock combinatorial proofs
that guarantee termination. By bounding the graph geometrically (i.e., restricting the
number of vertices to a finite set), we inherently prevent unbounded type generation
and avoid redundant iterative hierarchies.
-/

variable {V : Type} [Fintype V] [DecidableEq V]

/--
A generic edge in a graph over a finite type `V`.
Bounding the graph geometrically ensures that paths cannot grow indefinitely without forming cycles.
-/
structure GenericEdge (V : Type) where
  src : V
  dst : V
  weight : Int

/--
A path of a specific bounded length `n`.
By explicitly bounding the path length, we prevent unbounded type generation and enable
inductive proofs over finite structures.
-/
inductive BoundedPath (edges : List (GenericEdge V)) : Nat → V → V → Type where
  | nil (u : V) : BoundedPath edges 0 u u
  | cons {n : Nat} {w : V} (e : GenericEdge V) (h_in : e ∈ edges) (p : BoundedPath edges n e.dst w) : BoundedPath edges (n + 1) e.src w

def boundedPathWeight {edges : List (GenericEdge V)} {n : Nat} {u v : V} : BoundedPath edges n u v → Int
  | BoundedPath.nil _ => 0
  | BoundedPath.cons e _ p => e.weight + boundedPathWeight p
