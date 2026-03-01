import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Combinatorics.Pigeonhole
import NfValidate.FintypeGraph

variable {V : Type} [Fintype V] [DecidableEq V]
variable {edges : List (GenericEdge V)}

def pathVertices {n : Nat} {u v : V} : BoundedPath edges n u v → Fin (n + 1) → V
  | BoundedPath.nil _, _ => u
  | BoundedPath.cons e _ p, i =>
    if h : i.val = 0 then
      e.src
    else
      pathVertices p ⟨i.val - 1, by omega⟩

theorem path_has_duplicate (p : BoundedPath edges (Fintype.card V) u v) :
  ∃ (i j : Fin (Fintype.card V + 1)), i ≠ j ∧ pathVertices p i = pathVertices p j := by
  apply Fintype.exists_ne_map_eq_of_card_lt (pathVertices p)
  simp

def pathEdges {n : Nat} {u v : V} : BoundedPath edges n u v → List (GenericEdge V)
  | BoundedPath.nil _ => []
  | BoundedPath.cons e _ p => e :: pathEdges p

inductive ValidEdgeChain : List (GenericEdge V) → V → V → Prop where
  | nil (u : V) : ValidEdgeChain [] u u
  | cons (e : GenericEdge V) {es : List (GenericEdge V)} {w v : V} (heq : e.dst = w) (h : ValidEdgeChain es w v) : ValidEdgeChain (e :: es) e.src v

theorem pathEdges_valid {n : Nat} {u v : V} (p : BoundedPath edges n u v) :
  ValidEdgeChain (pathEdges p) u v := by
  induction p with
  | nil u => exact ValidEdgeChain.nil u
  | cons e h p ih => exact ValidEdgeChain.cons e rfl ih

-- A cycle is a path from a vertex to itself
def Cycle (edges : List (GenericEdge V)) (u : V) := Σ n, BoundedPath edges n u u

def extractCycle {n : Nat} {u v : V} (p : BoundedPath edges n u v) (i j : Fin (n + 1)) (hij : i.val < j.val) (heq : pathVertices p i = pathVertices p j) : Cycle edges (pathVertices p i) :=
  sorry

theorem negative_cycle_of_update {u v : V} (p : BoundedPath edges (Fintype.card V) u v)
  (h_update : boundedPathWeight p < 0) : -- simplified for now
  ∃ c : Cycle edges (pathVertices p ⟨0, by omega⟩), True := by
  sorry
