import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Pigeonhole
import Mathlib.Combinatorics.Pigeonhole
import NfValidate.FintypeGraph
import NfValidate.TelescopingSum

/-
  NegativeCycleExtraction.lean

  This module applies the Pigeonhole Principle to formally extract looping sub-paths
  from any sufficiently long path in the graph. By demonstrating that any path exceeding
  the number of vertices must revisit a node, we prove that the algorithm bounds itself
  within the finite set of variables, guaranteeing termination without infinite regress.
  This aligns with the mechanical validation philosophy of avoiding redundant iterative hierarchies.
-/

variable {V : Type} [Fintype V] [DecidableEq V]
variable {edges : List (GenericEdge V)}

def pathVertices {n : Nat} {u v : V} : BoundedPath edges n u v → Fin (n + 1) → V
  | BoundedPath.nil _, _ => u
  | BoundedPath.cons e _ p, i =>
    if h : i.val = 0 then
      e.src
    else
      pathVertices p ⟨i.val - 1, by omega⟩

/--
  Proves that any path of length equal to the number of vertices must contain a duplicate vertex.
  By relying on the Pigeonhole Principle over finite types, this theorem bypasses
  dependent type deadlocks and establishes a clean mathematical constraint for cycle extraction.
-/
theorem path_has_duplicate (p : BoundedPath edges (Fintype.card V) u v) :
  ∃ (i j : Fin (Fintype.card V + 1)), i ≠ j ∧ pathVertices p i = pathVertices p j := by
  apply Fintype.exists_ne_map_eq_of_card_lt
  simp

def pathEdges {n : Nat} {u v : V} : BoundedPath edges n u v → List (GenericEdge V)
  | BoundedPath.nil _ => []
  | BoundedPath.cons e _ p => e :: pathEdges p

theorem pathEdges_valid {n : Nat} {u v : V} (p : BoundedPath edges n u v) :
  EdgeChain (pathEdges p) u v := by
  induction p with
  | nil u => exact EdgeChain.nil u
  | cons e h_in p' ih => exact EdgeChain.cons e rfl ih

def Cycle (edges : List (GenericEdge V)) (u : V) := List (GenericEdge V)

def extractCycle {n : Nat} {u v : V} (p : BoundedPath edges n u v) (i j : Fin (n + 1)) (hij : i.val < j.val) (heq : pathVertices p i = pathVertices p j) : Cycle edges (pathVertices p i) :=
  (pathEdges p).drop i.val |>.take (j.val - i.val)

theorem negative_cycle_of_update {u v : V} (M : V → Int) (p : BoundedPath edges (Fintype.card V) u v)
  (i j : Fin (Fintype.card V + 1)) (hij : i.val < j.val) (heq : pathVertices p i = pathVertices p j)
  (pref suff : List (GenericEdge V)) (strict_e : GenericEdge V)
  (h_extract : extractCycle p i j hij heq = pref ++ strict_e :: suff)
  (h_chain : EdgeChain (extractCycle p i j hij heq) (pathVertices p i) (pathVertices p i))
  (h_parent_pref : ∀ e ∈ pref, M e.dst ≥ M e.src + e.weight)
  (h_parent_suff : ∀ e ∈ suff, M e.dst ≥ M e.src + e.weight)
  (h_strict : M strict_e.dst > M strict_e.src + strict_e.weight) :
  cycleWeightSum (extractCycle p i j hij heq) < 0 := by
  rw [h_extract] at h_chain ⊢
  exact cycleWeightSum_negative_of_strict_ineq M pref suff strict_e (pathVertices p i) h_chain h_parent_pref h_parent_suff h_strict
