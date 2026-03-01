import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

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

