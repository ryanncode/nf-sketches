import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

theorem evaluateClause_sound (vars : List Var) (constraints : List Constraint) (M : List (Var × Int))
  (h_eval : evaluateClause vars constraints = StratificationResult.success M) :
  SatisfiesGraph (lookup M) (buildEdges constraints) := by
  unfold evaluateClause at h_eval
  dsimp at h_eval
  revert h_eval
  -- split
  sorry
