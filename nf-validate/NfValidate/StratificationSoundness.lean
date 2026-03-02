import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

/--
Semantics of Quine's New Foundations Stratification.
A formula is stratified if there exists a typing context `ctx`
assigning an integer type level to each variable such that
the typing rules are satisfied.
-/
inductive IsStratified : Formula → (Var → Int) → Prop where
  | eq (x y : Var) (ctx : Var → Int)
      (h : ctx x = ctx y) : IsStratified (Formula.eq x y) ctx
  | mem (x y : Var) (ctx : Var → Int)
      (h : ctx y = ctx x + 1) : IsStratified (Formula.mem x y) ctx
  | neg (f : Formula) (ctx : Var → Int)
      (h : IsStratified f ctx) : IsStratified (Formula.neg f) ctx
  | conj (f g : Formula) (ctx : Var → Int)
      (hf : IsStratified f ctx) (hg : IsStratified g ctx) : IsStratified (Formula.conj f g) ctx
  | disj (f g : Formula) (ctx : Var → Int)
      (hf : IsStratified f ctx) (hg : IsStratified g ctx) : IsStratified (Formula.disj f g) ctx
  | impl (f g : Formula) (ctx : Var → Int)
      (hf : IsStratified f ctx) (hg : IsStratified g ctx) : IsStratified (Formula.impl f g) ctx
  | univ (x : Var) (f : Formula) (ctx : Var → Int)
      (h : IsStratified f ctx) : IsStratified (Formula.univ x f) ctx

/--
AST Compilation Containment: Equality
Proves that `extractConstraints` for an `eq` formula inserts the correct
0-difference constraint.
-/
theorem extractConstraints_eq (x y : Var) :
  { v1 := x, v2 := y, diff := 0 } ∈ extractConstraints (Formula.eq x y) := by
  simp [extractConstraints]

/--
AST Compilation Containment: Membership
Proves that `extractConstraints` for a `mem` formula inserts the correct
1-difference constraint.
-/
theorem extractConstraints_mem (x y : Var) :
  { v1 := x, v2 := y, diff := 1 } ∈ extractConstraints (Formula.mem x y) := by
  simp [extractConstraints]

/--
Graph Compilation Containment
Proves that if a constraint is in the extracted list, its bidirectional
edges are present in the generated graph.
-/
theorem buildEdges_containment (c : Constraint) (cs : List Constraint)
  (h : c ∈ cs) :
  { src := c.v1, dst := c.v2, weight := c.diff } ∈ buildEdges cs ∧
  { src := c.v2, dst := c.v1, weight := -c.diff } ∈ buildEdges cs := by
  induction cs with
  | nil => contradiction
  | cons c' cs' ih =>
    cases h with
    | head _ =>
      simp [buildEdges]
    | tail _ h_tail =>
      have ⟨h1, h2⟩ := ih h_tail
      simp [buildEdges]
      exact ⟨Or.inr (Or.inr h1), Or.inr (Or.inr h2)⟩

/--
Arithmetic Equivalence: Equality
Proves that if the bidirectional edges for an equality constraint
are satisfied by a distance map, the assigned levels must be equal.
-/
theorem stratified_eq_of_bounds (x y : Var) (ctx : Var → Int)
  (edges : List Edge)
  (h_sat : SatisfiesGraph ctx edges)
  (h_fwd : { src := x, dst := y, weight := 0 } ∈ edges)
  (h_bwd : { src := y, dst := x, weight := 0 } ∈ edges) :
  ctx x = ctx y := by
  have h1 := h_sat _ h_fwd
  have h2 := h_sat _ h_bwd
  dsimp [SatisfiesEdge] at h1 h2
  omega

/--
Arithmetic Equivalence: Membership
Proves that if the bidirectional edges for a membership constraint
are satisfied by a distance map, the assigned level of the right
variable must be exactly one greater than the left.
-/
theorem stratified_mem_of_bounds (x y : Var) (ctx : Var → Int)
  (edges : List Edge)
  (h_sat : SatisfiesGraph ctx edges)
  (h_fwd : { src := x, dst := y, weight := 1 } ∈ edges)
  (h_bwd : { src := y, dst := x, weight := -1 } ∈ edges) :
  ctx y = ctx x + 1 := by
  have h1 := h_sat _ h_fwd
  have h2 := h_sat _ h_bwd
  dsimp [SatisfiesEdge] at h1 h2
  omega

/--
Global Satisfiability Transfer
Proves that if a graph is satisfied, any subgraph is also satisfied.
-/
theorem satisfies_subgraph {edges sub_edges : List Edge} {d : Var → Int}
  (h_sat : SatisfiesGraph d edges)
  (h_sub : sub_edges ⊆ edges) :
  SatisfiesGraph d sub_edges := by
  intro e he
  exact h_sat e (h_sub he)

theorem buildEdges_append (cs1 cs2 : List Constraint) :
  buildEdges (cs1 ++ cs2) = buildEdges cs1 ++ buildEdges cs2 := by
  induction cs1 with
  | nil => simp [buildEdges]
  | cons c cs ih => simp [buildEdges, ih]

theorem satisfies_append_left {d : Var → Int} {E1 E2 : List Edge}
  (h : SatisfiesGraph d (E1 ++ E2)) : SatisfiesGraph d E1 := by
  intro e he
  apply h
  simp [he]

theorem satisfies_append_right {d : Var → Int} {E1 E2 : List Edge}
  (h : SatisfiesGraph d (E1 ++ E2)) : SatisfiesGraph d E2 := by
  intro e he
  apply h
  simp [he]

/--
Formula Satisfiability
Proves that if the constraint graph extracted from a formula is satisfied
by a distance map `d`, then the formula is stratified under `d`.
-/
theorem stratified_of_satisfies (f : Formula) (d : Var → Int)
  (h_sat : SatisfiesGraph d (buildEdges (extractConstraints f))) :
  IsStratified f d := by
  induction f with
  | eq x y =>
    apply IsStratified.eq
    apply stratified_eq_of_bounds x y d _ h_sat
    · have h := buildEdges_containment { v1 := x, v2 := y, diff := 0 } (extractConstraints (Formula.eq x y)) (by simp [extractConstraints])
      exact h.1
    · have h := buildEdges_containment { v1 := x, v2 := y, diff := 0 } (extractConstraints (Formula.eq x y)) (by simp [extractConstraints])
      exact h.2
  | mem x y =>
    apply IsStratified.mem
    apply stratified_mem_of_bounds x y d _ h_sat
    · have h := buildEdges_containment { v1 := x, v2 := y, diff := 1 } (extractConstraints (Formula.mem x y)) (by simp [extractConstraints])
      exact h.1
    · have h := buildEdges_containment { v1 := x, v2 := y, diff := 1 } (extractConstraints (Formula.mem x y)) (by simp [extractConstraints])
      exact h.2
  | neg f ih =>
    apply IsStratified.neg
    apply ih
    exact h_sat
  | conj f g ihf ihg =>
    apply IsStratified.conj
    · apply ihf
      have h_sat' : SatisfiesGraph d (buildEdges (extractConstraints f) ++ buildEdges (extractConstraints g)) := by
        rw [← buildEdges_append]
        exact h_sat
      exact satisfies_append_left h_sat'
    · apply ihg
      have h_sat' : SatisfiesGraph d (buildEdges (extractConstraints f) ++ buildEdges (extractConstraints g)) := by
        rw [← buildEdges_append]
        exact h_sat
      exact satisfies_append_right h_sat'
  | disj f g ihf ihg =>
    apply IsStratified.disj
    · apply ihf
      have h_sat' : SatisfiesGraph d (buildEdges (extractConstraints f) ++ buildEdges (extractConstraints g)) := by
        rw [← buildEdges_append]
        exact h_sat
      exact satisfies_append_left h_sat'
    · apply ihg
      have h_sat' : SatisfiesGraph d (buildEdges (extractConstraints f) ++ buildEdges (extractConstraints g)) := by
        rw [← buildEdges_append]
        exact h_sat
      exact satisfies_append_right h_sat'
  | impl f g ihf ihg =>
    apply IsStratified.impl
    · apply ihf
      have h_sat' : SatisfiesGraph d (buildEdges (extractConstraints f) ++ buildEdges (extractConstraints g)) := by
        rw [← buildEdges_append]
        exact h_sat
      exact satisfies_append_left h_sat'
    · apply ihg
      have h_sat' : SatisfiesGraph d (buildEdges (extractConstraints f) ++ buildEdges (extractConstraints g)) := by
        rw [← buildEdges_append]
        exact h_sat
      exact satisfies_append_right h_sat'
  | univ x f ih =>
    apply IsStratified.univ
    apply ih
    exact h_sat

/--
Final Synthesis
Bridging evaluation to soundness.
-/
theorem evaluateClause_sound (vars : List Var) (constraints : List Constraint) (M : List (Var × Int))
  (h_eval : evaluateClause vars constraints = StratificationResult.success M) :
  SatisfiesGraph (lookup M) (buildEdges constraints) := by
  unfold evaluateClause at h_eval

  -- Abstract the loop execution
  have h_loop : ∃ finalDist finalPred,
    evaluateClause.loop (buildEdges constraints) (vars.length - 1) (vars.map fun v => (v, 0)) [] = (finalDist, finalPred) := ⟨_, _, rfl⟩

  rcases h_loop with ⟨finalDist, finalPred, h_eq⟩

  -- Reduce let bindings so rw can match
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

  -- Rewrite h_eval with the abstracted result
  rw [h_eq] at h_eval
  dsimp only at h_eval

  -- Now analyze the final relaxEdges call
  have h_relax := relaxEdges_converged (buildEdges constraints) finalDist finalPred

  match h_relax_res : relaxEdges (buildEdges constraints) finalDist finalPred with
  | (d', p', hasCycle) =>
    -- In the success case, hasCycle must be false
    have h_hasCycle_false : hasCycle = false := by
      cases hasCycle
      · rfl
      · revert h_eval
        -- If hasCycle = true, then !true = false, so the if takes the else branch which is a failure
        -- but it equals success M
        intro h_eval
        have h_relax_true : (relaxEdges (buildEdges constraints) finalDist finalPred).2.2 = true := by
          rw [h_relax_res]
        rw [h_relax_true] at h_eval
        dsimp at h_eval
        split at h_eval
        · contradiction
        · contradiction

    -- M must be finalDist
    have h_M_eq : M = finalDist := by
      cases hasCycle
      · revert h_eval
        have h_relax_false : (relaxEdges (buildEdges constraints) finalDist finalPred).2.2 = false := by
          rw [h_relax_res]
        rw [h_relax_false]
        dsimp
        intro h_eval
        injection h_eval with h_eq_M
        exact h_eq_M.symm
      · contradiction

    -- Apply the invariant
    have h_converged := h_relax (by rw [h_relax_res]; exact h_hasCycle_false)

    -- Now show SatisfiesGraph
    intro e he
    have h_le := h_converged e he
    dsimp [SatisfiesEdge]

    subst h_M_eq

    have h_dist_eq : (relaxEdges (buildEdges constraints) M finalPred).1 = M := by
      apply foldl_false_dist_eq
      change (relaxEdges (buildEdges constraints) M finalPred).2.2 = false
      rw [h_relax_res]
      exact h_hasCycle_false

    rw [h_dist_eq] at h_le
    omega

theorem stratification_sound (f : Formula) (M : List (Var × Int))
  (h_eval : evaluateStratification f = StratificationResult.success M) :
  IsStratified f (lookup M) := by
  unfold evaluateStratification at h_eval
  have h_sat := evaluateClause_sound (getFormulaVars f) (extractConstraints f) M h_eval
  exact stratified_of_satisfies f (lookup M) h_sat
