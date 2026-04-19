import NfValidate
import NfValidate.GraphSemantics

/--
  Proves that looking up a key `k` in an association list after updating it with value `v`
  returns the updated value `v`.
-/
theorem lookup_update_eq (l : List (ScopedVar × Int)) (k : ScopedVar) (v : Int) :
  lookup (update l k v) k = v := by
  induction l with
  | nil =>
    unfold update lookup
    simp
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    unfold update
    split
    · unfold lookup
      simp
    · unfold lookup
      simp [*]

/--
  Proves that looking up a key `k'` in an association list after updating a distinct key `k`
  returns the original value of `k'` from the list.
-/
theorem lookup_update_neq (l : List (ScopedVar × Int)) (k k' : ScopedVar) (v : Int) (h_neq : k ≠ k') :
  lookup (update l k v) k' = lookup l k' := by
  induction l with
  | nil =>
    unfold update lookup
    split
    · next heq =>
      have := eq_of_beq heq
      subst this
      contradiction
    · rfl
  | cons hd tl ih =>
    rcases hd with ⟨k'', v''⟩
    unfold update
    split
    · next heq =>
      unfold lookup
      split
      · next heq2 =>
        have h1 : k = k'' := eq_of_beq heq
        have h2 : k' = k := eq_of_beq heq2
        subst h1 h2
        contradiction
      · next hneq2 =>
        have h1 : k = k'' := eq_of_beq heq
        subst h1
        simp [hneq2]
    · next hneq2 =>
      unfold lookup
      split
      · next heq3 => rfl
      · next hneq3 => exact ih

/--
  Proves that updating a distance map with a value `v` that is less than or equal to
  the current value at key `k` preserves or decreases the distance for any key `x`.
-/
theorem lookup_update_le (l : List (ScopedVar × Int)) (k : ScopedVar) (v : Int) (x : ScopedVar) (h : v ≤ lookup l k) :
  lookup (update l k v) x ≤ lookup l x := by
  induction l with
  | nil =>
    unfold update lookup at *
    split
    · next hx =>
      have hxk : x = k := eq_of_beq hx
      subst hxk
      exact h
    · exact Int.le_refl _
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    unfold update
    split
    · next heq =>
      unfold lookup
      split
      · next hx =>
        unfold lookup at h
        have heqk : k = k' := eq_of_beq heq
        have hxk : x = k := eq_of_beq hx
        subst heqk hxk
        simp at h
        simp
        exact h
      · next hnx =>
        have heqk : k = k' := eq_of_beq heq
        subst heqk
        simp [*]
    · next hneq =>
      unfold lookup
      split
      · exact Int.le_refl _
      · unfold lookup at h
        simp [*] at h
        exact ih h

/--
  Proves that relaxing edges via `foldl` monotonically decreases distances.
  For any vertex `v`, its distance after edge relaxations is less than or equal
  to its distance before the relaxations.
-/
theorem relaxEdges_foldl_monotone (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) (v : ScopedVar) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 v ≤ lookup dist v := by
  induction edges generalizing dist pred changed with
  | nil =>
    simp
  | cons e edges' ih =>
    simp
    split
    · next hlt =>
      have h1 := ih (update dist e.dst (lookup dist e.src + e.weight)) (updatePred pred e.dst e.src) true
      have h2 : lookup dist e.src + e.weight ≤ lookup dist e.dst := by omega
      have h3 := lookup_update_le dist e.dst (lookup dist e.src + e.weight) v h2
      exact Int.le_trans h1 h3
    · next hge =>
      have h1 := ih dist pred changed
      exact h1

/--
  Corollary of `relaxEdges_foldl_monotone`: executing a single full relaxation pass
  over all edges monotonically decreases the distances.
-/
theorem relaxEdges_monotone (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar))
  (v : ScopedVar) :
  lookup (relaxEdges edges dist pred).1 v ≤ lookup dist v := by
  unfold relaxEdges
  exact relaxEdges_foldl_monotone edges dist pred false v

/--
  Proves that if the `changed` flag is `true` before folding over edges,
  it will remain `true` after folding, regardless of whether any further
  relaxations occur.
-/
theorem foldl_changed_true (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, true)).2.2 = true := by
  induction edges generalizing dist pred with
  | nil => rfl
  | cons e edges' ih =>
    simp
    split
    · next hlt => exact ih _ _
    · next hge => exact ih _ _

/--
  If a single pass of Bellman-Ford edge relaxations results in no changes
  (indicated by the `changed` boolean remaining `false`), then the resulting
  distance map is strictly equal to the input distance map.
-/
theorem foldl_false_dist_eq (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)).2.2 = false →
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)).1 = dist := by
  intro h
  induction edges generalizing dist pred with
  | nil => rfl
  | cons e edges' ih =>
    simp at h
    simp
    split at h
    · next hlt =>
      have h_true := foldl_changed_true edges' (update dist e.dst (lookup dist e.src + e.weight)) (updatePred pred e.dst e.src)
      rw [h_true] at h
      contradiction
    · next hge =>
      simp [hge]
      exact ih dist pred h

/--
  If a single pass of Bellman-Ford edge relaxations results in no changes
  (indicated by the `changed` boolean remaining `false`), then all edges
  satisfy the triangle inequality constraint: `dist[v] <= dist[u] + weight(u, v)`.
-/
theorem relaxEdges_foldl_converged (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)).2.2 = false → ∀ e ∈ edges, lookup dist e.dst ≤ lookup dist e.src + e.weight := by
  intro h e he
  induction edges generalizing dist pred with
  | nil => contradiction
  | cons e' edges' ih =>
    simp at he
    simp at h
    split at h
    · next hlt =>
      have h_true := foldl_changed_true edges' (update dist e'.dst (lookup dist e'.src + e'.weight)) (updatePred pred e'.dst e'.src)
      rw [h_true] at h
      contradiction
    · next hge =>
      cases he with
      | inl heq =>
        subst heq
        omega
      | inr hin =>
        exact ih dist pred h hin

/--
  Corollary of `relaxEdges_foldl_converged`: if a full call to `relaxEdges`
  returns `changed = false`, then every edge in the graph satisfies the triangle
  inequality, meaning the shortest paths have converged.
-/
theorem relaxEdges_converged (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
  (relaxEdges edges dist pred).2.2 = false → ∀ e ∈ edges, lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup (relaxEdges edges dist pred).1 e.src + e.weight := by
  intro h e he
  unfold relaxEdges at h ⊢
  have h_eq := foldl_false_dist_eq edges dist pred h
  rw [h_eq]
  exact relaxEdges_foldl_converged edges dist pred h e he
