import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

theorem evaluateClause_sound (vars : List Var) (constraints : List Constraint) (M : List (Var × Int))
  (h_eval : evaluateClause vars constraints = StratificationResult.success M) :
  SatisfiesGraph (lookup M) (buildEdges constraints) := by
  unfold evaluateClause at h_eval
  dsimp only at h_eval
  -- let's abstract the loop result
  have h_loop : ∃ finalDist finalPred, 
    (evaluateClause.loop (buildEdges constraints) (vars.length - 1) (vars.map fun v => (v, 0)) []) = (finalDist, finalPred) := ⟨_, _, rfl⟩
  sorry
