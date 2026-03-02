import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

theorem evaluateClause_sound (vars : List Var) (constraints : List Constraint) (M : List (Var × Int))
  (h_eval : evaluateClause vars constraints = StratificationResult.success M) :
  SatisfiesGraph (lookup M) (buildEdges constraints) := by
  unfold evaluateClause at h_eval
  dsimp only at h_eval
  
  have h_loop : ∃ finalDist finalPred,
    evaluateClause.loop (buildEdges constraints) (vars.length - 1) (vars.map fun v => (v, 0)) [] = (finalDist, finalPred) := ⟨_, _, rfl⟩

  rcases h_loop with ⟨finalDist, finalPred, h_eq⟩

  -- change the type explicitly without let bindings
  change (
    match evaluateClause.loop (buildEdges constraints) (vars.length - 1) (List.map (fun v => (v, 0)) vars) [] with
    | (finalDist, finalPred) =>
      match relaxEdges (buildEdges constraints) finalDist finalPred with
      | (fst, fst_1, hasCycle) =>
        if (!hasCycle) = true then StratificationResult.success finalDist
        else
          have conflictNode := List.findSome? (fun e =>
            if lookup finalDist e.src + e.weight < lookup finalDist e.dst then some e.dst else none) (buildEdges constraints);
          match conflictNode with
          | some node => StratificationResult.failure (getCycleForward finalPred node vars.length) (buildEdges constraints)
          | none => StratificationResult.failure [] (buildEdges constraints)
  ) = StratificationResult.success M at h_eval
  
  -- now we can rewrite
  rw [h_eq] at h_eval
  sorry
