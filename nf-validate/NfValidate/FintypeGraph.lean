import Mathlib.Data.Fintype.Basic

variable {V : Type} [Fintype V] [DecidableEq V]

structure GenericEdge (V : Type) where
  src : V
  dst : V
  weight : Int

inductive BoundedPath (edges : List (GenericEdge V)) : Nat → V → V → Type where
  | nil (u : V) : BoundedPath edges 0 u u
  | cons {n : Nat} {w : V} (e : GenericEdge V) (h_in : e ∈ edges) (p : BoundedPath edges n e.dst w) : BoundedPath edges (n + 1) e.src w

def boundedPathWeight {edges : List (GenericEdge V)} {n : Nat} {u v : V} : BoundedPath edges n u v → Int
  | BoundedPath.nil _ => 0
  | BoundedPath.cons e _ p => e.weight + boundedPathWeight p
