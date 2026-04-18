import NfValidate
import NfValidate.GraphSemantics

theorem lookup_update_eq (l : List (ScopedVar × Int)) (k : ScopedVar) (v : Int) :
  lookup (update l k v) k = v := sorry

theorem lookup_update_neq (l : List (ScopedVar × Int)) (k k' : ScopedVar) (v : Int) (h_neq : k ≠ k') :
  lookup (update l k v) k' = lookup l k' := sorry

theorem lookup_update_le (l : List (ScopedVar × Int)) (k : ScopedVar) (v : Int) (x : ScopedVar) (h : v ≤ lookup l k) :
  lookup (update l k v) x ≤ lookup l x := sorry

theorem relaxEdges_foldl_monotone (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) (v : ScopedVar) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 v ≤ lookup dist v := sorry

theorem relaxEdges_monotone (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar))
  (v : ScopedVar) :
  lookup (relaxEdges edges dist pred).1 v ≤ lookup dist v := sorry

theorem foldl_changed_true (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, true)).2.2 = true := sorry

theorem foldl_false_dist_eq (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)).1 = dist := sorry

theorem relaxEdges_foldl_converged (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)).2.2 = false → ∀ e ∈ edges, lookup dist e.dst ≤ lookup dist e.src + e.weight := sorry

theorem relaxEdges_converged (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  (relaxEdges edges dist pred).2.2 = false → ∀ e ∈ edges, lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup (relaxEdges edges dist pred).1 e.src + e.weight := sorry
