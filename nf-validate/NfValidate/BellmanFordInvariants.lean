import NfValidate
import NfValidate.GraphSemantics

-- 1. Map Properties

theorem lookup_update_eq (l : List (Var × Int)) (k : Var) (v : Int) :
  lookup (update l k v) k = v := by
  induction l with
  | nil =>
    unfold update lookup
    simp
  | cons hd tl ih =>
    unfold update
    split
    · next h =>
      unfold lookup
      simp [h]
    · next h =>
      unfold lookup
      simp [h, ih]

theorem lookup_update_neq (l : List (Var × Int)) (k k' : Var) (v : Int) (h_neq : k ≠ k') :
  lookup (update l k v) k' = lookup l k' := by
  induction l with
  | nil =>
    unfold update lookup
    have h_not : (k' == k) = false := by
      cases h : (k' == k)
      · rfl
      · have h_eq : k' = k := eq_of_beq h
        subst h_eq
        contradiction
    simp [h_not]
    unfold lookup
    rfl
  | cons hd tl ih =>
    match hd with
    | (k'', v'') =>
      unfold update
      split
      · next h_eq =>
        have h_k_eq : k = k'' := eq_of_beq h_eq
        subst h_k_eq
        unfold lookup
        have h_not : (k' == k) = false := by
          cases h_c : (k' == k)
          · rfl
          · have h_eq2 : k' = k := eq_of_beq h_c
            subst h_eq2
            contradiction
        simp [h_not]
      · next h_neq2 =>
        unfold lookup
        split
        · next h_eq3 => rfl
        · next h_neq3 => exact ih

-- 2. Relaxation Monotonicity

theorem lookup_update_le (l : List (Var × Int)) (k : Var) (v : Int) (x : Var) (h : v ≤ lookup l k) :
  lookup (update l k v) x ≤ lookup l x := by
  cases h_eq : (x == k)
  · have h_neq : k ≠ x := by
      intro hc
      subst hc
      simp at h_eq
    rw [lookup_update_neq l k x v h_neq]
    omega
  · have h_eq2 : x = k := eq_of_beq h_eq
    subst h_eq2
    rw [lookup_update_eq]
    exact h

theorem relaxEdges_foldl_monotone (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) (changed : Bool) (v : Var) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 v ≤ lookup dist v := by
  revert dist pred changed
  induction edges with
  | nil =>
    intro dist pred changed
    simp
  | cons e es ih =>
    intro dist pred changed
    simp only [List.foldl]
    split
    · next h_lt =>
      have h1 := ih (update dist e.dst (lookup dist e.src + e.weight)) (updatePred pred e.dst e.src) true
      have h2 : lookup (update dist e.dst (lookup dist e.src + e.weight)) v ≤ lookup dist v := by
        apply lookup_update_le
        omega
      exact Int.le_trans h1 h2
    · next h_ge =>
      exact ih dist pred changed

theorem relaxEdges_monotone (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var))
  (v : Var) :
  lookup (relaxEdges edges dist pred).1 v ≤ lookup dist v := by
  unfold relaxEdges
  exact relaxEdges_foldl_monotone edges dist pred false v

-- 3. Convergence Condition

theorem foldl_changed_true (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, true)).2.2 = true := by
  revert dist pred
  induction edges with
  | nil =>
    intro dist pred
    simp
  | cons e es ih =>
    intro dist pred
    simp only [List.foldl]
    split
    · next h_lt => exact ih _ _
    · next h_ge => exact ih _ _

theorem foldl_false_dist_eq (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) (changed : Bool) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).2.2 = false →
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 = dist := by
  revert dist pred changed
  induction edges with
  | nil =>
    intro dist pred changed h
    simp
  | cons e es ih =>
    intro dist pred changed
    simp only [List.foldl]
    split
    · next h_lt =>
      intro h
      have h_true := foldl_changed_true es (update dist e.dst (lookup dist e.src + e.weight)) (updatePred pred e.dst e.src)
      rw [h_true] at h
      contradiction
    · next h_ge =>
      intro h
      exact ih dist pred changed h

theorem relaxEdges_foldl_converged (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) (changed : Bool) :
  (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).2.2 = false → ∀ e ∈ edges,
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 e.dst ≤
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 e.src + e.weight := by
  revert dist pred changed
  induction edges with
  | nil =>
    intro dist pred changed h e h_in
    contradiction
  | cons e' es ih =>
    intro dist pred changed
    simp only [List.foldl]
    split
    · next h_lt =>
      intro h e h_in
      have h_true := foldl_changed_true es (update dist e'.dst (lookup dist e'.src + e'.weight)) (updatePred pred e'.dst e'.src)
      rw [h_true] at h
      contradiction
    · next h_ge =>
      intro h e h_in
      have h_ge_le : lookup dist e'.dst ≤ lookup dist e'.src + e'.weight := by omega
      cases h_in with
      | head _ =>
        have h_eq := foldl_false_dist_eq es dist pred changed h
        have h_eq_full : (es.foldl (fun (accD, accP, changed) e =>
          let du := lookup accD e.src
          let dv := lookup accD e.dst
          if du + e.weight < dv then
            (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
          else
            (accD, accP, changed)
        ) (dist, pred, changed)).1 = dist := h_eq
        rw [h_eq_full]
        exact h_ge_le
      | tail _ h_in_es =>
        exact ih dist pred changed h e h_in_es

theorem relaxEdges_converged (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) :
  (relaxEdges edges dist pred).2.2 = false → ∀ e ∈ edges, lookup (relaxEdges edges dist pred).1 e.dst ≤ lookup (relaxEdges edges dist pred).1 e.src + e.weight := by
  unfold relaxEdges
  exact relaxEdges_foldl_converged edges dist pred false
