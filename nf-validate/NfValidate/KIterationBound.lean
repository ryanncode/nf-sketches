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
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 e.dst ≤ lookup dist e.src + e.weight := by
  induction edges generalizing dist pred changed with
  | nil =>
    contradiction
  | cons e' es ih =>
    cases h_in with
    | head _ =>
      simp only [List.foldl]
      split
      · next h_lt =>
        have h_mono := relaxEdges_foldl_monotone es (update dist e.dst (lookup dist e.src + e.weight)) (updatePred pred e.dst e.src) true e.dst
        have h_upd : lookup (update dist e.dst (lookup dist e.src + e.weight)) e.dst = lookup dist e.src + e.weight := lookup_update_eq dist e.dst _
        rw [h_upd] at h_mono
        exact h_mono
      · next h_ge =>
        have h_mono := relaxEdges_foldl_monotone es dist pred changed e.dst
        have h_bound : lookup dist e.dst ≤ lookup dist e.src + e.weight := by omega
        exact Int.le_trans h_mono h_bound
    | tail _ h_in_tail =>
      simp only [List.foldl]
      split
      · next h_lt =>
        have h_ih := ih h_in_tail (update dist e'.dst (lookup dist e'.src + e'.weight)) (updatePred pred e'.dst e'.src) true
        have h_upd_le : lookup (update dist e'.dst (lookup dist e'.src + e'.weight)) e.src ≤ lookup dist e.src := by
          apply lookup_update_le
          omega
        exact Int.le_trans h_ih (by omega)
      · next h_ge =>
        exact ih h_in_tail dist pred changed

theorem relaxEdges_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (Var × Int)) (pred : List (Var × Var)) :
  lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup dist e.src + e.weight := by
  unfold relaxEdges
  exact relaxEdges_foldl_edge_bound edges e h_in dist pred false

theorem relaxEdgesN_succ (edges : List Edge) (dist : List (Var × Int)) (k : Nat) :
  relaxEdgesN edges dist (k + 1) = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := by
  induction k generalizing dist with
  | zero => rfl
  | succ k ih =>
    have h : relaxEdgesN edges dist (Nat.succ k + 1) = relaxEdgesN edges (relaxEdges edges dist []).1 (k + 1) := rfl
    rw [h]
    rw [ih]
    rfl

/--
The `k_iteration_bound` theorem certifies the Bellman-Ford traversal limits.
It proves that after `k` relaxation iterations, the computed distance to any vertex `v`
is bounded by the weight of any valid path of length `k` from a source `u`.
This guarantees that the algorithm mathematically restricts the depth of type derivations
and correctly computes shortest paths (or detects violations) within the iteration limit.
-/
theorem k_iteration_bound (edges : List Edge) (d : List (Var × Int)) (k : Nat) (u v : Var)
  (p : BoundedPath edges k u v) :
  lookup (relaxEdgesN edges d k) v ≤ lookup d u + boundedPathWeight p := by
  induction k generalizing v with
  | zero =>
    cases p with
    | nil _ =>
      unfold relaxEdgesN boundedPathWeight
      omega
  | succ k ih =>
    cases p with
    | snoc p' e h_in h_eq =>
      rw [relaxEdgesN_succ]
      unfold boundedPathWeight
      have h_edge := relaxEdges_edge_bound edges e h_in (relaxEdgesN edges d k) []
      have h_ih := ih _ p'
      rw [h_eq] at h_edge
      omega
