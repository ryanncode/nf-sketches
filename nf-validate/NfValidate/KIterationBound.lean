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

lemma relaxEdgesN_succ_lem (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) :
  relaxEdgesN edges (relaxEdges edges dist []).1 k = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := by
  induction k generalizing dist with
  | zero => rfl
  | succ k ih =>
    dsimp [relaxEdgesN]
    rw [ih (relaxEdges edges dist []).1]

theorem relaxEdgesN_succ (edges : List Edge) (dist : List (ScopedVar × Int)) (k : Nat) :
  relaxEdgesN edges dist (k + 1) = (relaxEdges edges (relaxEdgesN edges dist k) []).1 := by
  exact relaxEdgesN_succ_lem edges dist k

def relaxStep (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (e : Edge) :
  List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool :=
  let du := lookup acc.1 e.src
  let dv := lookup acc.1 e.dst
  if du + e.weight < dv then
    (update acc.1 e.dst (du + e.weight), updatePred acc.2.1 e.dst e.src, true)
  else
    acc

lemma relaxStep_bound (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (e : Edge) :
  lookup (relaxStep acc e).1 e.dst ≤ lookup acc.1 e.src + e.weight := by
  dsimp [relaxStep]
  split
  · next h => rw [lookup_update_eq]
  · next h => linarith

lemma relaxStep_monotone_step (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (e : Edge) (v : ScopedVar) :
  lookup (relaxStep acc e).1 v ≤ lookup acc.1 v := by
  dsimp [relaxStep]
  split
  · next h => apply lookup_update_le; linarith
  · next h => rfl

lemma relaxEdges_foldl_monotone_gen (edges : List Edge) (acc : List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool) (v : ScopedVar) :
  lookup (edges.foldl relaxStep acc).1 v ≤ lookup acc.1 v := by
  induction edges generalizing acc with
  | nil => rfl
  | cons e edges ih =>
    have h1 := ih (relaxStep acc e)
    have h2 := relaxStep_monotone_step acc e v
    change lookup (edges.foldl relaxStep (relaxStep acc e)).1 v ≤ _
    linarith

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

theorem relaxEdges_edge_bound (edges : List Edge) (e : Edge) (h_in : e ∈ edges) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup dist e.src + e.weight := by
  exact relaxEdges_foldl_edge_bound edges e h_in dist pred false

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
