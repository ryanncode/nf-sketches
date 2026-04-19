import NfValidate

/-!
# Graph Semantics for Weak Stratification

This module maps geometric paths and constraint satisfiability directly to the definitions
of weak stratification. Under Bowler's acyclic translation, we evaluate structural rules (e.g.,
`x ∈ y ⇒ t(x) < t(y)` under general formulations or strict difference bindings) as algebraic
constraints on edge weights. Satisfiability of the acyclic graph is thus algebraically
equivalent to the existence of a valid weak type assignment.
-/

/--
Represents a valid sequence of edges from vertex `u` to vertex `v`.
In the context of the algebraic constraint translation, a path represents a
chain of relative type level constraints (typing derivations) between variables.
-/
inductive Path (edges : List Edge) : ScopedVar → ScopedVar → Type where
  | nil (u : ScopedVar) : Path edges u u
  | cons {w : ScopedVar} (e : Edge) (h_in : e ∈ edges) (p : Path edges e.dst w) : Path edges e.src w

/--
Calculates the sum of the weights of the edges in a given path.
-/
def pathWeight {edges : List Edge} {u v : ScopedVar} : Path edges u v → Int
  | Path.nil _ => 0
  | Path.cons e _ p => e.weight + pathWeight p

/--
A cycle is a path from a vertex to itself.
Algebraically, this represents a sequence of type constraints that relate a variable's
type back to itself, which is critical for detecting stratification violations.
-/
abbrev Cycle (edges : List Edge) (u : ScopedVar) := Path edges u u

/--
A negative cycle is a cycle whose total weight is strictly less than 0.
-/
structure NegativeCycle (edges : List Edge) where
  u : ScopedVar
  cycle : Cycle edges u
  is_negative : pathWeight cycle < 0

/--
A context/distance map `d` satisfies an edge `e` if `d(e.dst) - d(e.src) ≤ e.weight`.
Equivalently: `d(e.dst) ≤ d(e.src) + e.weight`.
-/
def SatisfiesEdge (d : ScopedVar → Int) (e : Edge) : Prop :=
  d e.dst - d e.src ≤ e.weight

/--
A context `d` satisfies a whole graph (list of edges) if it satisfies every edge in the graph.
Under the algebraic constraint translation, this means the context `d` forms a valid
stratification assignment (type assignment) that strictly adheres to the weak stratification
rules encoded by the acyclic graph structure.
-/
def SatisfiesGraph (d : ScopedVar → Int) (edges : List Edge) : Prop :=
  ∀ e ∈ edges, SatisfiesEdge d e

/--
Path Inequality Lemma: If a context `d` satisfies a graph,
then for any `Path` from `u` to `v` with total weight `W`, `d(v) - d(u) ≤ W`.
-/
theorem path_inequality {edges : List Edge} {u v : ScopedVar} (d : ScopedVar → Int)
  (h_sat : SatisfiesGraph d edges) (p : Path edges u v) :
  d v - d u ≤ pathWeight p := by
  induction p with
  | nil u =>
    simp [pathWeight]
  | cons e h_in p ih =>
    have h_edge : d e.dst - d e.src ≤ e.weight := h_sat e h_in
    have h_path : d _ - d e.dst ≤ pathWeight p := ih
    change d _ - d e.src ≤ e.weight + pathWeight p
    omega

theorem no_valid_context_for_negative_cycle {edges : List Edge}
  (nc : NegativeCycle edges) (d : ScopedVar → Int) :
  ¬ SatisfiesGraph d edges := by
  intro h_sat
  have h_path := path_inequality d h_sat nc.cycle
  have h_neg := nc.is_negative
  omega

theorem equality_semantics {edges : List Edge} {x y : ScopedVar} (d : ScopedVar → Int)
  (h_sat : SatisfiesGraph d edges)
  (h_fwd : ∃ e1 ∈ edges, e1.src = x ∧ e1.dst = y ∧ e1.weight = 0)
  (h_bwd : ∃ e2 ∈ edges, e2.src = y ∧ e2.dst = x ∧ e2.weight = 0) :
  d x = d y := by
  rcases h_fwd with ⟨e1, h1_in, h1_src, h1_dst, h1_w⟩
  rcases h_bwd with ⟨e2, h2_in, h2_src, h2_dst, h2_w⟩
  have hd1 : d e1.dst - d e1.src ≤ e1.weight := h_sat e1 h1_in
  have hd2 : d e2.dst - d e2.src ≤ e2.weight := h_sat e2 h2_in
  rw [h1_src, h1_dst, h1_w] at hd1
  rw [h2_src, h2_dst, h2_w] at hd2
  omega
