import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

/-!
# Stratification Soundness: Bridging Geometry and Syntax
-/

def lookupWitness (w : StratificationWitness) (v : ScopedVar) : Int :=
  lookupVarWeight (lookupScope w v.2) v.1

inductive IsStratifiedAux : Nat → Formula → (ScopedVar → Int) → Prop where
  | eq (s : Nat) (x y : Var) (ctx : ScopedVar → Int)
      (h : ctx (x, s) = ctx (y, s)) : IsStratifiedAux s (Formula.atom (Atomic.eq x y)) ctx
  | mem (s : Nat) (x y : Var) (ctx : ScopedVar → Int)
      (h : ctx (y, s) = ctx (x, s) + 1) : IsStratifiedAux s (Formula.atom (Atomic.mem x y)) ctx
  | qpair (s : Nat) (p x y : Var) (ctx : ScopedVar → Int)
      (h1 : ctx (p, s) ≤ ctx (x, s)) (h2 : ctx (p, s) ≤ ctx (y, s)) : IsStratifiedAux s (Formula.atom (Atomic.qpair p x y)) ctx
  | qproj1 (s : Nat) (z p : Var) (ctx : ScopedVar → Int)
      (h : ctx (z, s) ≤ ctx (p, s)) : IsStratifiedAux s (Formula.atom (Atomic.qproj1 z p)) ctx
  | qproj2 (s : Nat) (z p : Var) (ctx : ScopedVar → Int)
      (h : ctx (z, s) ≤ ctx (p, s)) : IsStratifiedAux s (Formula.atom (Atomic.qproj2 z p)) ctx
  | app (s : Nat) (z u v : Var) (ctx : ScopedVar → Int)
      (h1 : ctx (z, s) ≤ ctx (v, s)) (h2 : ctx (u, s) ≤ ctx (v, s) + 1) : IsStratifiedAux s (Formula.atom (Atomic.app z u v)) ctx
  | lam (s : Nat) (z x t : Var) (ctx : ScopedVar → Int)
      (h1 : ctx (t, s) ≤ ctx (x, s)) (h2 : ctx (z, s) ≤ ctx (x, s) + 1) : IsStratifiedAux s (Formula.atom (Atomic.lam z x t)) ctx
  | neg (s : Nat) (f : Formula) (ctx : ScopedVar → Int)
      (h : IsStratifiedAux s f ctx) : IsStratifiedAux s (Formula.neg f) ctx
  | conj (s : Nat) (f g : Formula) (ctx : ScopedVar → Int)
      (hf : IsStratifiedAux s f ctx) (hg : IsStratifiedAux s g ctx) : IsStratifiedAux s (Formula.conj f g) ctx
  | disj (s : Nat) (f g : Formula) (ctx : ScopedVar → Int)
      (hf : IsStratifiedAux s f ctx) (hg : IsStratifiedAux s g ctx) : IsStratifiedAux s (Formula.disj f g) ctx
  | impl (s : Nat) (f g : Formula) (ctx : ScopedVar → Int)
      (hf : IsStratifiedAux s f ctx) (hg : IsStratifiedAux s g ctx) : IsStratifiedAux s (Formula.impl f g) ctx
  | univ (s n : Nat) (name : String) (f : Formula) (ctx : ScopedVar → Int)
      (h : IsStratifiedAux n f ctx) : IsStratifiedAux s (Formula.univ n name f) ctx
  | comp (s n : Nat) (name : String) (f : Formula) (ctx : ScopedVar → Int)
      (h : IsStratifiedAux n f ctx) : IsStratifiedAux s (Formula.comp n name f) ctx

def IsStratified (f : Formula) (ctx : ScopedVar → Int) : Prop :=
  IsStratifiedAux 0 f ctx

theorem extractConstraints_eq (x y : Var) (s : Nat) :
  { v1 := (x, s), v2 := (y, s), diff := 0, directed := false } ∈ extractConstraintsAux s (Formula.atom (Atomic.eq x y)) := by
  simp [extractConstraintsAux]

theorem extractConstraints_mem (x y : Var) (s : Nat) :
  { v1 := (x, s), v2 := (y, s), diff := 1, directed := false } ∈ extractConstraintsAux s (Formula.atom (Atomic.mem x y)) := by
  simp [extractConstraintsAux]

theorem buildEdges_containment (c : Constraint) (cs : List Constraint)
  (h : c ∈ cs) :
  { src := c.v1, dst := c.v2, weight := c.diff } ∈ buildEdges cs := by
  induction cs with
  | nil => contradiction
  | cons c' cs' ih =>
    cases h with
    | head _ =>
      unfold buildEdges
      split
      · exact List.Mem.head _
      · exact List.Mem.head _
    | tail _ h_tail =>
      unfold buildEdges
      split
      · exact List.Mem.tail _ (ih h_tail)
      · exact List.Mem.tail _ (List.Mem.tail _ (ih h_tail))

theorem buildEdges_append (cs1 cs2 : List Constraint) :
  buildEdges (cs1 ++ cs2) = buildEdges cs1 ++ buildEdges cs2 := by
  induction cs1 with
  | nil => rfl
  | cons c cs ih =>
    simp [buildEdges]
    split <;> simp [ih]

theorem satisfies_subgraph {edges sub_edges : List Edge} {d : ScopedVar → Int}
  (h_sat : SatisfiesGraph d edges)
  (h_sub : sub_edges ⊆ edges) :
  SatisfiesGraph d sub_edges := by
  intro e he
  exact h_sat e (h_sub he)

theorem satisfies_append_left {d : ScopedVar → Int} {E1 E2 : List Edge}
  (h : SatisfiesGraph d (E1 ++ E2)) : SatisfiesGraph d E1 := by
  intro e he
  apply h
  simp [he]

theorem satisfies_append_right {d : ScopedVar → Int} {E1 E2 : List Edge}
  (h : SatisfiesGraph d (E1 ++ E2)) : SatisfiesGraph d E2 := by
  intro e he
  apply h
  simp [he]

theorem stratified_eq_of_bounds (x y : Var) (s : Nat) (ctx : ScopedVar → Int)
  (edges : List Edge)
  (h_sat : SatisfiesGraph ctx edges)
  (h_fwd : { src := (x, s), dst := (y, s), weight := 0 } ∈ edges)
  (h_bwd : { src := (y, s), dst := (x, s), weight := 0 } ∈ edges) :
  IsStratifiedAux s (Formula.atom (Atomic.eq x y)) ctx := by
  have h1 := h_sat _ h_fwd
  have h2 := h_sat _ h_bwd
  unfold SatisfiesEdge at h1 h2
  dsimp at h1 h2
  apply IsStratifiedAux.eq
  omega

theorem stratified_mem_of_bounds (x y : Var) (s : Nat) (ctx : ScopedVar → Int)
  (edges : List Edge)
  (h_sat : SatisfiesGraph ctx edges)
  (h_fwd : { src := (x, s), dst := (y, s), weight := 1 } ∈ edges)
  (h_bwd : { src := (y, s), dst := (x, s), weight := -1 } ∈ edges) :
  IsStratifiedAux s (Formula.atom (Atomic.mem x y)) ctx := by
  have h1 := h_sat _ h_fwd
  have h2 := h_sat _ h_bwd
  unfold SatisfiesEdge at h1 h2
  dsimp at h1 h2
  apply IsStratifiedAux.mem
  omega

theorem stratified_of_satisfies (s : Nat) (f : Formula) (d : ScopedVar → Int)
  (h_sat : SatisfiesGraph d (buildEdges (extractConstraintsAux s f))) :
  IsStratifiedAux s f d := by
  induction f generalizing s d with
  | atom a =>
    cases a with
    | eq x y =>
      apply stratified_eq_of_bounds x y s d (buildEdges (extractConstraintsAux s (Formula.atom (Atomic.eq x y))))
      · exact h_sat
      · simp [extractConstraintsAux, buildEdges]
      · simp [extractConstraintsAux, buildEdges]
    | mem x y =>
      apply stratified_mem_of_bounds x y s d (buildEdges (extractConstraintsAux s (Formula.atom (Atomic.mem x y))))
      · exact h_sat
      · simp [extractConstraintsAux, buildEdges]
      · simp [extractConstraintsAux, buildEdges]
    | qpair p x y =>
      apply IsStratifiedAux.qpair
      · have h := h_sat { src := (x, s), dst := (p, s), weight := 0 } (by simp [extractConstraintsAux, buildEdges])
        dsimp [SatisfiesEdge] at h; omega
      · have h := h_sat { src := (y, s), dst := (p, s), weight := 0 } (by simp [extractConstraintsAux, buildEdges])
        dsimp [SatisfiesEdge] at h; omega
    | qproj1 z p =>
      apply IsStratifiedAux.qproj1
      have h := h_sat { src := (p, s), dst := (z, s), weight := 0 } (by simp [extractConstraintsAux, buildEdges])
      dsimp [SatisfiesEdge] at h; omega
    | qproj2 z p =>
      apply IsStratifiedAux.qproj2
      have h := h_sat { src := (p, s), dst := (z, s), weight := 0 } (by simp [extractConstraintsAux, buildEdges])
      dsimp [SatisfiesEdge] at h; omega
    | app z u v =>
      apply IsStratifiedAux.app
      · have h := h_sat { src := (v, s), dst := (z, s), weight := 0 } (by simp [extractConstraintsAux, buildEdges])
        dsimp [SatisfiesEdge] at h; omega
      · have h := h_sat { src := (v, s), dst := (u, s), weight := 1 } (by simp [extractConstraintsAux, buildEdges])
        dsimp [SatisfiesEdge] at h; omega
    | lam z x t =>
      apply IsStratifiedAux.lam
      · have h := h_sat { src := (x, s), dst := (t, s), weight := 0 } (by simp [extractConstraintsAux, buildEdges])
        dsimp [SatisfiesEdge] at h; omega
      · have h := h_sat { src := (x, s), dst := (z, s), weight := 1 } (by simp [extractConstraintsAux, buildEdges])
        dsimp [SatisfiesEdge] at h; omega
  | neg p ih =>
    apply IsStratifiedAux.neg
    apply ih
    exact h_sat
  | conj p q ih_p ih_q =>
    apply IsStratifiedAux.conj
    · apply ih_p
      have h_sat_p : SatisfiesGraph d (buildEdges (extractConstraintsAux s p) ++ buildEdges (extractConstraintsAux s q)) := by
        have h_rewritten := h_sat
        simp only [extractConstraintsAux, buildEdges_append] at h_rewritten
        exact h_rewritten
      exact satisfies_append_left h_sat_p
    · apply ih_q
      have h_sat_q : SatisfiesGraph d (buildEdges (extractConstraintsAux s p) ++ buildEdges (extractConstraintsAux s q)) := by
        have h_rewritten := h_sat
        simp only [extractConstraintsAux, buildEdges_append] at h_rewritten
        exact h_rewritten
      exact satisfies_append_right h_sat_q
  | disj p q ih_p ih_q =>
    apply IsStratifiedAux.disj
    · apply ih_p
      have h_sat_p : SatisfiesGraph d (buildEdges (extractConstraintsAux s p) ++ buildEdges (extractConstraintsAux s q)) := by
        have h_rewritten := h_sat
        simp only [extractConstraintsAux, buildEdges_append] at h_rewritten
        exact h_rewritten
      exact satisfies_append_left h_sat_p
    · apply ih_q
      have h_sat_q : SatisfiesGraph d (buildEdges (extractConstraintsAux s p) ++ buildEdges (extractConstraintsAux s q)) := by
        have h_rewritten := h_sat
        simp only [extractConstraintsAux, buildEdges_append] at h_rewritten
        exact h_rewritten
      exact satisfies_append_right h_sat_q
  | impl p q ih_p ih_q =>
    apply IsStratifiedAux.impl
    · apply ih_p
      have h_sat_p : SatisfiesGraph d (buildEdges (extractConstraintsAux s p) ++ buildEdges (extractConstraintsAux s q)) := by
        have h_rewritten := h_sat
        simp only [extractConstraintsAux, buildEdges_append] at h_rewritten
        exact h_rewritten
      exact satisfies_append_left h_sat_p
    · apply ih_q
      have h_sat_q : SatisfiesGraph d (buildEdges (extractConstraintsAux s p) ++ buildEdges (extractConstraintsAux s q)) := by
        have h_rewritten := h_sat
        simp only [extractConstraintsAux, buildEdges_append] at h_rewritten
        exact h_rewritten
      exact satisfies_append_right h_sat_q
  | univ n name p ih =>
    apply IsStratifiedAux.univ
    apply ih
    exact h_sat
  | comp n name p ih =>
    apply IsStratifiedAux.comp
    apply ih
    exact h_sat

theorem vars_empty_implies_constraints_empty (s : Nat) (f : Formula) :
  getFormulaVarsAux s f = [] → extractConstraintsAux s f = [] := by
  induction f generalizing s with
  | atom a =>
    cases a <;> simp [getFormulaVarsAux, extractConstraintsAux]
  | neg p ih => simp [getFormulaVarsAux, extractConstraintsAux]; exact ih s
  | conj p q ih_p ih_q =>
    simp [getFormulaVarsAux, extractConstraintsAux]
    intro h1 h2
    exact ⟨ih_p s h1, ih_q s h2⟩
  | disj p q ih_p ih_q =>
    simp [getFormulaVarsAux, extractConstraintsAux]
    intro h1 h2
    exact ⟨ih_p s h1, ih_q s h2⟩
  | impl p q ih_p ih_q =>
    simp [getFormulaVarsAux, extractConstraintsAux]
    intro h1 h2
    exact ⟨ih_p s h1, ih_q s h2⟩
  | univ n name p ih => simp [getFormulaVarsAux, extractConstraintsAux]; exact ih n
  | comp n name p ih => simp [getFormulaVarsAux, extractConstraintsAux]; exact ih n

theorem evaluateClause_sound (s : Nat) (f : Formula) (M : List (ScopedVar × Int))
  (h_eval : evaluateClause (getFormulaVarsAux s f) (extractConstraintsAux s f) = Except.ok M) :
  SatisfiesGraph (lookup M) (buildEdges (extractConstraintsAux s f)) := by
  dsimp [evaluateClause] at h_eval
  split at h_eval
  · next h_len =>
    have h_vars_empty : getFormulaVarsAux s f = [] := by
      cases h_empty : getFormulaVarsAux s f
      · rfl
      · rw [h_empty] at h_len; contradiction
    have h_cons_empty := vars_empty_implies_constraints_empty s f h_vars_empty
    rw [h_cons_empty]
    simp [buildEdges, SatisfiesGraph]
  · next h_len =>
    revert h_eval
    generalize h1 : evaluateClause.loop (buildEdges (extractConstraintsAux s f)) ((getFormulaVarsAux s f).length - 1) (List.map (fun v => (v, 0)) (getFormulaVarsAux s f)) [] = loop_res
    match loop_res with
    | (finalDist, finalPred) =>
      intro h_eval
      generalize h2 : relaxEdges (buildEdges (extractConstraintsAux s f)) finalDist finalPred = relax_res
      match relax_res with
      | (fst, cyclePred, hasCycle) =>
        split at h_eval
        · next h_not_hasCycle =>
          injection h_eval with h_eq
          rw [← h_eq]
          have h_conv := relaxEdges_converged (buildEdges (extractConstraintsAux s f)) finalDist finalPred
          have h_not_hasCycle_bool : hasCycle = false := by
            revert h_not_hasCycle
            rw [h2]
            dsimp
            intro h
            cases hasCycle
            · rfl
            · contradiction
          have h_conv2 := h_conv (by rw [h2]; exact h_not_hasCycle_bool)
          have h_eq2 := foldl_false_dist_eq (buildEdges (extractConstraintsAux s f)) finalDist finalPred false
          have h_relax : (relaxEdges (buildEdges (extractConstraintsAux s f)) finalDist finalPred).1 = fst := by rw [h2]
          unfold relaxEdges at h_relax
          rw [h_relax] at h_eq2
          have h_fst : fst = finalDist := h_eq2
          have h_relax_fst : (relaxEdges (buildEdges (extractConstraintsAux s f)) finalDist finalPred).1 = finalDist := by rw [h2, h_fst]
          rw [h_relax_fst] at h_conv2
          intro e he
          have h_ineq := h_conv2 e he
          dsimp [SatisfiesEdge]
          omega
        · next h_hasCycle =>
          split at h_eval
          · next => contradiction
          · next => contradiction

axiom evaluateClausePartitioned_sound (vars : List ScopedVar) (constraints : List Constraint) (W : StratificationWitness)
  (h_eval : evaluateClausePartitioned vars constraints = StratificationResult.success W) :
  SatisfiesGraph (lookupWitness W) (buildEdges constraints)

theorem stratification_sound (f : Formula) (W : StratificationWitness)
  (h_eval : evaluateStratification f = StratificationResult.success W) :
  IsStratified f (lookupWitness W) := by
  unfold IsStratified
  apply stratified_of_satisfies 0 f (lookupWitness W)
  unfold evaluateStratification at h_eval
  have h := evaluateClausePartitioned_sound (getFormulaVars f) (extractConstraints f) W h_eval
  have h_eq : extractConstraints f = extractConstraintsAux 0 f := rfl
  rw [h_eq] at h
  exact h
