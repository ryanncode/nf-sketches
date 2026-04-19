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

/--
A structural witness representing a strictly bounded path in the constraint graph.
The path must consist of exactly `k` edges. This restricts recursive cycle-finding
to at most `V` steps, guaranteeing algorithm termination.
-/
inductive KBoundedPath (edges : List Edge) : Nat → ScopedVar → ScopedVar → Type where
  | nil (u : ScopedVar) : KBoundedPath edges 0 u u
  | snoc {k : Nat} {u w : ScopedVar} (p : KBoundedPath edges k u w) (e : Edge) (h_in : e ∈ edges) (h_eq : e.src = w) : KBoundedPath edges (k + 1) u e.dst

/--
Calculates the aggregated weight of a path bounded by exactly `k` edges.
Used to identify algebraic contradictions (negative cycles) when traversing graph structures.
-/
def kBoundedPathWeight {edges : List Edge} {k : Nat} {u v : ScopedVar} : KBoundedPath edges k u v → Int
  | .nil _ => 0
  | .snoc p e _ _ => kBoundedPathWeight p + e.weight

/--
Executes the Bellman-Ford edge relaxation phase exactly `k` times.
Produces the distance mapping dynamically evolved over `k` synchronous graph sweeps.
-/
def relaxEdgesN (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) : List (ScopedVar × Int) :=
  match k with
  | 0 => dist
  | k' + 1 => relaxEdgesN edges (relaxEdges edges dist []).1 k'

/--
Lemma mapping structural list recursion to functional iteration sequences.
Validates that running relaxations `k` times on a single swept graph is equivalent to
sweeping a `k`-times relaxed graph.
-/
lemma relaxEdgesN_succ_lem (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) :
  relaxEdgesN edges (relaxEdges edges dist []).1 k = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := by
  induction k generalizing dist with
  | zero => rfl
  | succ k ih =>
    dsimp [relaxEdgesN]
    rw [ih (relaxEdges edges dist []).1]

/--
Theorem certifying that incrementing the iteration bound strictly correlates
to appending an entire graph relaxation pass to the evaluation cycle.
-/
theorem relaxEdgesN_succ (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) :
  relaxEdgesN edges dist (k + 1) = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := by
  exact relaxEdgesN_succ_lem edges dist k

/--
Purely functional abstraction of a single directed edge constraint relaxation.
Updates distances mathematically based strictly on topological cost derivations.
-/
def relaxStep (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (e : Edge) :
  List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool :=
  let du := lookup acc.1 e.src
  let dv := lookup acc.1 e.dst
  if du + e.weight < dv then
    (update acc.1 e.dst (du + e.weight), updatePred acc.2.1 e.dst e.src, true)
  else
    acc

/--
Constraint guarantee verifying that after relaxing an edge `e`, the graph destination node
is definitively bounded below or equal to the source distance augmented by the edge weight.
-/
lemma relaxStep_bound (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (e : Edge) :
  lookup (relaxStep acc e).1 e.dst ≤ lookup acc.1 e.src + e.weight := by
  dsimp [relaxStep]
  split
  · next h => rw [lookup_update_eq]
  · next h => linarith

/--
Stepwise guarantee asserting the fundamental non-increasing property of topological constraint relaxations.
Distances can only decrease natively as graph limits tighten.
-/
lemma relaxStep_monotone_step (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (e : Edge) (v : ScopedVar) :
  lookup (relaxStep acc e).1 v ≤ lookup acc.1 v := by
  dsimp [relaxStep]
  split
  · next h => apply lookup_update_le; linarith
  · next h => rfl

/--
Generalizes `relaxStep_monotone_step` over iterative folds, guaranteeing holistic downward
monotonicity across lists of unrolled abstract syntax constraints.
-/
lemma relaxEdges_foldl_monotone_gen (edges : List Edge) (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (v : ScopedVar) :
  lookup (edges.foldl relaxStep acc).1 v ≤ lookup acc.1 v := by
  induction edges generalizing acc with
  | nil => rfl
  | cons e edges ih =>
    have h1 := ih (relaxStep acc e)
    have h2 := relaxStep_monotone_step acc e v
    change lookup (edges.foldl relaxStep (relaxStep acc e)).1 v ≤ _
    linarith

/--
Bounds structural fold executions algorithmically. Ensures recursive sub-folds respect
topological distance bounds dictated inherently by the unrolled AST constraints.
-/
lemma relaxEdges_foldl_edge_bound_gen (remaining : List Edge) (e : Edge) (h_in : e ∈ remaining)
  (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (dist : List (ScopedVar × Int))
  (h_le : ∀ v, lookup acc.1 v ≤ lookup dist v) :
  lookup (remaining.foldl relaxStep acc).1 e.dst ≤ lookup dist e.src + e.weight := by
  induction remaining generalizing acc with
  | nil => contradiction
  | cons e' remaining ih =>
    cases h_in with
    | head _ =>
      have h1 := relaxEdges_foldl_monotone_gen remaining (relaxStep acc e) e.dst
      have h2 := relaxStep_bound acc e
      have h3 := h_le e.src
      change lookup (remaining.foldl relaxStep (relaxStep acc e)).1 e.dst ≤ _
      linarith
    | tail _ h_in =>
      have h_le_next : ∀ v, lookup (relaxStep acc e').1 v ≤ lookup dist v := by
        intro v
        have h1 := relaxStep_monotone_step acc e' v
        have h2 := h_le v
        linarith
      have h_ih := ih h_in (relaxStep acc e') h_le_next
      change lookup (remaining.foldl relaxStep (relaxStep acc e')).1 e.dst ≤ _
      exact h_ih

/--
Proof that executing a single global relaxation sweep strictly obeys the topological
limit mapping source variables directly to destination variables. The destination will always
bind tightly to at most `src + weight`.
-/
theorem relaxEdges_foldl_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 e.dst ≤ lookup dist e.src + e.weight := by
  change lookup (edges.foldl relaxStep (dist, pred, changed)).1 e.dst ≤ _
  apply relaxEdges_foldl_edge_bound_gen edges e h_in (dist, pred, changed) dist
  intro v
  rfl

/--
Top-level semantic equivalent of `relaxEdges_foldl_edge_bound` applying directly to the pure
`relaxEdges` graph interface rather than its unrolled tuple fold structure.
-/
theorem relaxEdges_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup dist e.src + e.weight := by
  exact relaxEdges_foldl_edge_bound edges e h_in dist pred false

/--
The pivotal K-Iteration Bound Theorem.
Establishes the fundamental limit correlating iteration depth, distance mappings, and graph paths.
If there exists a topological path `p` of length `k` spanning `u` to `v`, executing the solver `k` times
guarantees the distance `d(v)` is mathematically forced to be `≤ d(u) + weight(p)`.
This geometric bound strictly regulates the type extraction process and ensures finite model convergence.
-/
theorem k_iteration_bound (edges : List Edge) (d : List (ScopedVar × Int)) (k : Nat) (u v : ScopedVar)
  (p : KBoundedPath edges k u v) :
  lookup (relaxEdgesN edges d k) v ≤ lookup d u + kBoundedPathWeight p := by
  induction p with
  | nil u =>
    simp [relaxEdgesN, kBoundedPathWeight]
  | @snoc k_ p_u p_w p' e h_in h_eq ih =>
    simp [kBoundedPathWeight]
    rw [relaxEdgesN_succ]
    have h1 := relaxEdges_edge_bound edges e h_in (relaxEdgesN edges d k_) []
    rw [h_eq] at h1
    linarith
