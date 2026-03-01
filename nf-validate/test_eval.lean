import NfValidate
import NfValidate.BellmanFordInvariants
import NfValidate.StratificationSoundness

theorem evaluateClause_sound (vars : List Var) (constraints : List Constraint) (M : List (Var × Int))
  (h_eval : evaluateClause vars constraints = StratificationResult.success M) :
  SatisfiesGraph (lookup M) (buildEdges constraints) := by
  unfold evaluateClause at h_eval
  revert h_eval
  let edges := buildEdges constraints
  let n := vars.length
  let initialDist := vars.map (fun v => (v, (0 : Int)))
  let initialPred : List (Var × Var) := []
  let (finalDist, finalPred) := evaluateClause.loop edges (n - 1) initialDist initialPred
  intro h_eval
  have h_not_cycle : (relaxEdges edges finalDist finalPred).2.2 = false := by
    cases h : (relaxEdges edges finalDist finalPred).2.2
    · rfl
    · rw [h] at h_eval
      dsimp at h_eval
      contradiction
  have h_eq : M = finalDist := by
    cases h : (relaxEdges edges finalDist finalPred).2.2
    · rw [h] at h_eval
      dsimp at h_eval
      injection h_eval with h_eq
      exact h_eq.symm
    · rw [h] at h_eval
      dsimp at h_eval
      contradiction
  subst h_eq
  exact relaxEdges_converged edges finalDist finalPred h_not_cycle
