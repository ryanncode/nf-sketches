import NfValidate.BellmanFordInvariants

theorem relaxEdges_foldl_edge_bound (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) (changed : Bool)
  (e : Edge) (h_in : e ∈ edges) :
  lookup (edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, changed)).1 e.dst ≤ lookup dist e.src + e.weight := by
  revert dist pred changed
  induction edges with
  | nil =>
    intro dist pred changed h_in
    contradiction
  | cons e' es ih =>
    intro dist pred changed h_in
    simp only [List.foldl]
    cases h_in with
    | head _ =>
      split
      · next h_lt =>
        have h_mono := relaxEdges_foldl_monotone es (update dist e.dst (lookup dist e.src + e.weight)) (updatePred pred e.dst e.src) true e.dst
        have h_upd : lookup (update dist e.dst (lookup dist e.src + e.weight)) e.dst = lookup dist e.src + e.weight := lookup_update_eq dist e.dst _
        rw [h_upd] at h_mono
        exact h_mono
      · next h_ge =>
        have h_mono := relaxEdges_foldl_monotone es dist pred changed e.dst
        omega
    | tail _ h_in_tail =>
      split
      · next h_lt =>
        have h_ih := ih (update dist e'.dst (lookup dist e'.src + e'.weight)) (updatePred pred e'.dst e'.src) true h_in_tail
        have h_upd_le : lookup (update dist e'.dst (lookup dist e'.src + e'.weight)) e.src ≤ lookup dist e.src := by
          apply lookup_update_le
          omega
        exact Int.le_trans h_ih (by omega)
      · next h_ge =>
        exact ih dist pred changed h_in_tail

