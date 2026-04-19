import NfValidate
import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants
import NfValidate.TelescopingSum
import NfValidate.NegativeCycleExtraction
import NfValidate.KIterationBound
import NfValidate.BowlerTranslation

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

theorem evaluateClause_general_sound (vars : List ScopedVar) (constraints : List Constraint) (M : List (ScopedVar × Int))
  (h_vars_cons : vars = [] → constraints = [])
  (h_eval : evaluateClause vars constraints = Except.ok M) :
  SatisfiesGraph (lookup M) (buildEdges constraints) := by
  dsimp [evaluateClause] at h_eval
  split at h_eval
  · next h_len =>
    have h_vars_empty : vars = [] := by
      cases h_empty : vars
      · rfl
      · rw [h_empty] at h_len; contradiction
    have h_cons_empty := h_vars_cons h_vars_empty
    rw [h_cons_empty]
    simp [buildEdges, SatisfiesGraph]
  · next h_len =>
    revert h_eval
    generalize h1 : evaluateClause.loop (buildEdges constraints) (vars.length - 1) (List.map (fun v => (v, 0)) vars) [] = loop_res
    match loop_res with
    | (finalDist, finalPred) =>
      intro h_eval
      generalize h2 : relaxEdges (buildEdges constraints) finalDist finalPred = relax_res
      match relax_res with
      | (fst, cyclePred, hasCycle) =>
        split at h_eval
        · next h_not_hasCycle =>
          injection h_eval with h_eq
          rw [← h_eq]
          have h_conv := relaxEdges_converged (buildEdges constraints) finalDist finalPred
          have h_not_hasCycle_bool : hasCycle = false := by
            revert h_not_hasCycle
            rw [h2]
            dsimp
            intro h
            cases hasCycle
            · rfl
            · contradiction
          have h_conv2 := h_conv (by rw [h2]; exact h_not_hasCycle_bool)
          have h_foldl : (relaxEdges (buildEdges constraints) finalDist finalPred).2.2 = false := by
            rw [h2]
            exact h_not_hasCycle_bool
          have h_eq2 := foldl_false_dist_eq (buildEdges constraints) finalDist finalPred false h_foldl
          have h_relax : (relaxEdges (buildEdges constraints) finalDist finalPred).1 = fst := by rw [h2]
          unfold relaxEdges at h_relax
          rw [h_relax] at h_eq2
          have h_fst : fst = finalDist := h_eq2
          have h_relax_fst : (relaxEdges (buildEdges constraints) finalDist finalPred).1 = finalDist := by rw [h2, h_fst]
          rw [h_relax_fst] at h_conv2
          intro e he
          have h_ineq := h_conv2 e he
          dsimp [SatisfiesEdge]
          omega
        · next h_hasCycle =>
          split at h_eval
          · next => contradiction
          · next => contradiction

theorem extractConstraintsAux_scope_parity (s : Nat) (f : Formula) (c : Constraint)
  (h_in : c ∈ extractConstraintsAux s f) :
  c.v1.2 = c.v2.2 := by
  induction f generalizing s with
  | atom a =>
    cases a <;> simp [extractConstraintsAux] at h_in
    · rcases h_in with rfl | rfl <;> rfl
    · rcases h_in with rfl | rfl <;> rfl
    · rcases h_in with rfl | rfl <;> rfl
    · rcases h_in with rfl <;> rfl
    · rcases h_in with rfl <;> rfl
    · rcases h_in with rfl | rfl <;> rfl
    · rcases h_in with rfl | rfl <;> rfl
  | neg p ih =>
    exact ih s h_in
  | conj p q ih_p ih_q =>
    simp [extractConstraintsAux] at h_in
    rcases h_in with h | h
    · exact ih_p s h
    · exact ih_q s h
  | disj p q ih_p ih_q =>
    simp [extractConstraintsAux] at h_in
    rcases h_in with h | h
    · exact ih_p s h
    · exact ih_q s h
  | impl p q ih_p ih_q =>
    simp [extractConstraintsAux] at h_in
    rcases h_in with h | h
    · exact ih_p s h
    · exact ih_q s h
  | univ n name p ih =>
    exact ih n h_in
  | comp n name p ih =>
    exact ih n h_in

theorem lookup_map_dist (dist' : List (ScopedVar × Int)) (v : Var) (s : Nat)
  (h_scope : ∀ x ∈ dist', x.1.2 = s) :
  lookupVarWeight (dist'.map (fun ⟨⟨v', _⟩, weight⟩ => (v', weight))) v = lookup dist' (v, s) := by
  induction dist' with
  | nil => rfl
  | cons hd tl ih =>
    rcases hd with ⟨⟨v1, s1⟩, w⟩
    have hs' : s1 = s := by
      have : ((v1, s1), w) ∈ ((v1, s1), w) :: tl := List.Mem.head _
      exact h_scope _ this
    rw [hs']
    dsimp [lookupVarWeight, lookup]
    by_cases h : v = v1
    · have h_eq1 : (v == v1) = true := by
        simp [h]
      have h_eq2 : (((v, s) : ScopedVar) == ((v1, s) : ScopedVar)) = true := by
        simp [h]
      rw [h_eq1, h_eq2, if_pos rfl, if_pos rfl]
    · have h_neq1 : (v == v1) = false := by
        simp [h]
      have h_neq2 : (((v, s) : ScopedVar) == ((v1, s) : ScopedVar)) = false := by
        simp [h]
      rw [h_neq1, h_neq2, if_neg (by simp), if_neg (by simp)]
      apply ih
      intro x hx
      exact h_scope x (List.Mem.tail _ hx)

theorem evalScopes_lookupScope_acc (vars : List ScopedVar) (constraints : List Constraint)
  (ss : List Nat) (acc : List (Nat × List (Var × Int))) (w : StratificationWitness)
  (h_eval : evalScopes vars constraints ss acc = StratificationResult.success w)
  (s : Nat) (l : List (Var × Int))
  (h_in : (s, l) ∈ acc)
  (h_first : ∀ l', (s, l') ∈ acc → l' = l)
  (h_not_in_ss : s ∉ ss) :
  lookupScope w s = l := by
  induction ss generalizing acc with
  | nil =>
    dsimp [evalScopes] at h_eval
    have h_w : acc = w := by injection h_eval
    subst h_w
    clear h_eval h_not_in_ss
    induction acc with
    | nil => contradiction
    | cons hd tl ih =>
      rcases hd with ⟨s', l'⟩
      dsimp [lookupScope]
      by_cases h_eq : s = s'
      · subst h_eq
        have : l' = l := h_first l' (List.Mem.head _)
        subst this
        simp
      · have h_neq_b : (s == s') = false := by simp [h_eq]
        simp [h_neq_b]
        apply ih
        · cases h_in with
          | head => contradiction
          | tail _ h_in_tl => exact h_in_tl
        · intro l'' h_in''
          exact h_first l'' (List.Mem.tail _ h_in'')
  | cons s' rest ih =>
    dsimp [evalScopes] at h_eval
    split at h_eval
    · next dist'' heq' =>
      apply ih _ h_eval
      · simp [List.mem_cons]
        right
        exact h_in
      · intro l'' h_in''
        simp [List.mem_cons] at h_in''
        cases h_in'' with
        | inl h_eq =>
          have h_s_eq : s = s' := h_eq.left
          subst h_s_eq
          simp [List.mem_cons] at h_not_in_ss
        | inr h_in_acc =>
          exact h_first l'' h_in_acc
      · intro h_in_rest
        simp [List.mem_cons] at h_not_in_ss
        exact h_not_in_ss.right h_in_rest
    · contradiction

theorem lookupWitness_eq_eval_dist (vars : List ScopedVar) (constraints : List Constraint)
  (ss : List Nat) (acc : List (Nat × List (Var × Int))) (w : StratificationWitness)
  (h_eval : evalScopes vars constraints ss acc = StratificationResult.success w)
  (s : Nat) (dist' : List (ScopedVar × Int))
  (heq : evaluateClause (vars.filter (fun v => v.2 == s)) (constraints.filter (fun c => c.v1.2 == s)) = Except.ok dist')
  (hs : s ∈ ss)
  (h_nodup : ∀ s', s' ∈ ss → s' ∉ acc.map Prod.fst)
  (h_ss_nodup : List.Nodup ss)
  (h_scope : ∀ x ∈ dist', x.1.2 = s)
  (v : Var) :
  lookupWitness w (v, s) = lookup dist' (v, s) := by
  dsimp [lookupWitness]
  induction ss generalizing acc with
  | nil => contradiction
  | cons s' rest ih =>
    dsimp [evalScopes] at h_eval
    split at h_eval
    · next dist'' heq' =>
      have h_cases : s = s' ∨ s ∈ rest := by
        simp [List.mem_cons] at hs; exact hs
      cases h_cases with
      | inl h_eq_s =>
        subst h_eq_s
        have h_dist_eq : dist' = dist'' := by
          rw [heq] at heq'
          injection heq'
        subst h_dist_eq
        have h_lookup : lookupScope w s = dist'.map (fun ⟨⟨v', _⟩, weight⟩ => (v', weight)) := by
          apply evalScopes_lookupScope_acc vars constraints rest _ w h_eval s _
          · simp [List.mem_cons]
          · intro l' h_in
            simp [List.mem_cons] at h_in
            cases h_in with
            | inl h_eq => exact h_eq
            | inr h_in_acc =>
              have h_s_not_in : s ∉ acc.map Prod.fst := by
                apply h_nodup s
                simp [List.mem_cons]
              have h_s_in : s ∈ acc.map Prod.fst := by
                -- manually map
                have h_mem_map : (s, l') ∈ acc → s ∈ acc.map Prod.fst := by
                  intro h
                  simp [List.mem_map]
                  exists l'
                exact h_mem_map h_in_acc
              contradiction
          · have h_nodup_rest : s ∉ rest := by
              cases h_ss_nodup with
              | cons h_not_in h_rest_nodup =>
                intro h_in_rest
                exact h_not_in s h_in_rest rfl
            exact h_nodup_rest
        rw [h_lookup]
        apply lookup_map_dist dist' v s h_scope
      | inr h_in_rest =>
        apply ih _ h_eval h_in_rest
        · intro s'' hs''
          have h_not_in := h_nodup s'' (by simp [List.mem_cons, hs''])
          intro h_in_map
          simp [List.map, List.mem_cons] at h_in_map
          cases h_in_map with
          | inl h_eq =>
            have h_s_eq : s'' = s' := h_eq
            rw [h_s_eq] at hs''
            cases h_ss_nodup with
            | cons h_s_not_in_rest h_rest_nodup =>
              exact h_s_not_in_rest s' hs'' rfl
          | inr h_in_acc =>
            have : s'' ∈ acc.map Prod.fst := by
              rcases h_in_acc with ⟨x, hx⟩
              simp [List.mem_map]
              exists x
            exact h_not_in this
        · cases h_ss_nodup with
          | cons _ h_rest => exact h_rest
    · contradiction

theorem buildEdges_scope_preserve (s : Nat) (cs : List Constraint)
  (h_scope : ∀ c ∈ cs, c.v1.2 = s ∧ c.v2.2 = s)
  (e : Edge) (h_in : e ∈ buildEdges cs) :
  e.src.2 = s ∧ e.dst.2 = s := by
  induction cs with
  | nil =>
    simp [buildEdges] at h_in
  | cons c cs ih =>
    unfold buildEdges at h_in
    split at h_in
    · simp at h_in
      cases h_in with
      | inl h_eq =>
        have h_c := h_scope c (List.Mem.head _)
        subst h_eq
        exact h_c
      | inr h_in_rest =>
        apply ih
        · intro c' hc'
          exact h_scope c' (List.Mem.tail _ hc')
        · exact h_in_rest
    · simp at h_in
      cases h_in with
      | inl h_eq =>
        have h_c := h_scope c (List.Mem.head _)
        subst h_eq
        exact h_c
      | inr h_rest =>
        cases h_rest with
        | inl h_eq =>
          have h_c := h_scope c (List.Mem.head _)
          subst h_eq
          exact ⟨h_c.right, h_c.left⟩
        | inr h_in_rest =>
          apply ih
          · intro c' hc'
            exact h_scope c' (List.Mem.tail _ hc')
          · exact h_in_rest

theorem evalScopes_sound (vars : List ScopedVar) (constraints : List Constraint)
  (ss : List Nat) (acc : List (Nat × List (Var × Int))) (w : StratificationWitness)
  (h_eval : evalScopes vars constraints ss acc = StratificationResult.success w)
  (h_vars_cons : ∀ s, vars.filter (fun v => v.2 == s) = [] → constraints.filter (fun c => c.v1.2 == s) = [])
  (s : Nat) (hs : s ∈ ss)
  (h_nodup : ∀ s', s' ∈ ss → s' ∉ acc.map Prod.fst)
  (h_ss_nodup : List.Nodup ss)
  (h_scope : ∀ s dist', evaluateClause (vars.filter (fun v => v.2 == s)) (constraints.filter (fun c => c.v1.2 == s)) = Except.ok dist' → ∀ x ∈ dist', x.1.2 = s)
  (h_cons_scope : ∀ c ∈ constraints, c.v1.2 = c.v2.2) :
  SatisfiesGraph (lookupWitness w) (buildEdges (constraints.filter (fun c => c.v1.2 == s))) := by
  induction ss generalizing acc with
  | nil => contradiction
  | cons s' rest ih =>
    have h_eval_orig := h_eval
    dsimp [evalScopes] at h_eval
    split at h_eval
    · next dist' heq =>
      have h_cases : s = s' ∨ s ∈ rest := by
        simp [List.mem_cons] at hs; exact hs
      cases h_cases with
      | inl h_eq_s =>
        subst h_eq_s
        have h_sat_dist := evaluateClause_general_sound (vars.filter (fun v => v.2 == s)) (constraints.filter (fun c => c.v1.2 == s)) dist' (h_vars_cons s) heq
        intro e he
        have h_sat_e := h_sat_dist e he
        unfold SatisfiesEdge at h_sat_e ⊢
        have he_scope : e.src.2 = s ∧ e.dst.2 = s := by
          apply buildEdges_scope_preserve s (constraints.filter (fun c => c.v1.2 == s))
          · intro c hc
            simp [List.mem_filter] at hc
            have h1 := hc.right
            have h2 := h_cons_scope c hc.left
            rw [h1] at h2
            exact ⟨hc.right, h2.symm⟩
          · exact he
        have h1 : lookupWitness w e.src = lookup dist' e.src := by
          have h_src_eq : e.src = (e.src.1, s) := by
            rcases e_src_eq : e.src with ⟨v, n⟩
            have he_scope_left := he_scope.left
            rw [e_src_eq] at he_scope_left
            have h_n : n = s := he_scope_left
            subst h_n
            rfl
          rw [h_src_eq]
          apply lookupWitness_eq_eval_dist vars constraints (s :: rest) acc w h_eval_orig s dist' heq (by simp) h_nodup h_ss_nodup (h_scope s dist' heq) e.src.1
        have h2 : lookupWitness w e.dst = lookup dist' e.dst := by
          have h_dst_eq : e.dst = (e.dst.1, s) := by
            rcases e_dst_eq : e.dst with ⟨v, n⟩
            have he_scope_right := he_scope.right
            rw [e_dst_eq] at he_scope_right
            have h_n : n = s := he_scope_right
            subst h_n
            rfl
          rw [h_dst_eq]
          apply lookupWitness_eq_eval_dist vars constraints (s :: rest) acc w h_eval_orig s dist' heq (by simp) h_nodup h_ss_nodup (h_scope s dist' heq) e.dst.1
        rw [h1, h2]
        exact h_sat_e
      | inr hs_tail =>
        apply ih ((s', dist'.map (fun ⟨⟨v, _⟩, weight⟩ => (v, weight))) :: acc) h_eval hs_tail
        · intro s'' hs''
          have h_not_in_orig := h_nodup s'' (by simp [List.mem_cons, hs''])
          intro h_in_map
          simp [List.map, List.mem_cons] at h_in_map
          cases h_in_map with
          | inl h_eq =>
            have h_s_eq : s'' = s' := h_eq
            rw [h_s_eq] at hs''
            cases h_ss_nodup with
            | cons h_not_in_rest _ => exact h_not_in_rest s' hs'' rfl
          | inr h_in_acc =>
            have : s'' ∈ acc.map Prod.fst := by
              rcases h_in_acc with ⟨x, hx⟩
              simp [List.mem_map]
              exists x
            exact h_not_in_orig this
        · cases h_ss_nodup with
          | cons _ h_rest => exact h_rest
    · contradiction

theorem filter_scope_empty_vars_constraints (f : Formula) (s n : Nat) :
  (getFormulaVarsAux n f).filter (fun v => v.2 == s) = [] →
  (extractConstraintsAux n f).filter (fun c => c.v1.2 == s) = [] := by
  induction f generalizing n s with
  | atom a =>
    cases a <;> simp [getFormulaVarsAux, extractConstraintsAux]
  | neg p ih =>
    exact ih s n
  | conj p q ih_p ih_q =>
    simp [getFormulaVarsAux, extractConstraintsAux]
    intro h_p h_q
    have hp_eq : (getFormulaVarsAux n p).filter (fun v => v.2 == s) = [] := by
      simp [List.filter_eq_nil_iff]
      exact h_p
    have hq_eq : (getFormulaVarsAux n q).filter (fun v => v.2 == s) = [] := by
      simp [List.filter_eq_nil_iff]
      exact h_q
    have h1 := ih_p s n hp_eq
    have h2 := ih_q s n hq_eq
    rw [List.filter_eq_nil_iff] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩
  | disj p q ih_p ih_q =>
    simp [getFormulaVarsAux, extractConstraintsAux]
    intro h_p h_q
    have hp_eq : (getFormulaVarsAux n p).filter (fun v => v.2 == s) = [] := by
      simp [List.filter_eq_nil_iff]
      exact h_p
    have hq_eq : (getFormulaVarsAux n q).filter (fun v => v.2 == s) = [] := by
      simp [List.filter_eq_nil_iff]
      exact h_q
    have h1 := ih_p s n hp_eq
    have h2 := ih_q s n hq_eq
    rw [List.filter_eq_nil_iff] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩
  | impl p q ih_p ih_q =>
    simp [getFormulaVarsAux, extractConstraintsAux]
    intro h_p h_q
    have hp_eq : (getFormulaVarsAux n p).filter (fun v => v.2 == s) = [] := by
      simp [List.filter_eq_nil_iff]
      exact h_p
    have hq_eq : (getFormulaVarsAux n q).filter (fun v => v.2 == s) = [] := by
      simp [List.filter_eq_nil_iff]
      exact h_q
    have h1 := ih_p s n hp_eq
    have h2 := ih_q s n hq_eq
    rw [List.filter_eq_nil_iff] at h1 h2
    simp at h1 h2
    exact ⟨h1, h2⟩
  | univ n' name p ih =>
    intro h
    exact ih s n' h
  | comp n' name p ih =>
    intro h
    exact ih s n' h

theorem mem_nub {α : Type} [DecidableEq α] (x : α) (l : List α) : x ∈ nub l ↔ x ∈ l := by
  unfold nub
  induction l generalizing x with
  | nil => simp [List.foldr]
  | cons hd tl ih =>
    dsimp [List.foldr]
    have h_contains : (tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) []).contains hd = true ↔ hd ∈ tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) [] := by
      exact List.contains_iff_mem
    by_cases h_in_tl : hd ∈ tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) []
    · have h_true : (tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) []).contains hd = true := by
        exact h_contains.mpr h_in_tl
      rw [h_true]
      dsimp
      have h_in_tl_orig : hd ∈ tl := (ih hd).mp h_in_tl
      rw [ih]
      constructor
      · intro h_x
        exact List.Mem.tail _ h_x
      · intro h_x
        cases h_x with
        | head _ => exact h_in_tl_orig
        | tail _ h_in_tl_x => exact h_in_tl_x
    · have h_false : (tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) []).contains hd = false := by
        cases h_eq : (tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) []).contains hd
        · rfl
        · have := h_contains.mp h_eq
          contradiction
      rw [h_false]
      dsimp
      simp only [List.mem_cons]
      rw [ih]

theorem nodup_nub {α : Type} [DecidableEq α] (l : List α) : List.Nodup (nub l) := by
  unfold nub
  induction l with
  | nil => exact List.nodup_nil
  | cons hd tl ih =>
    dsimp [List.foldr]
    cases h : (tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) []).contains hd
    · have h_not_in : ¬hd ∈ tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) [] := by
        intro h_in
        have := List.contains_iff_mem.mpr h_in
        rw [this] at h; contradiction
      change List.Nodup (if false then tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) [] else hd :: tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) [])
      dsimp
      constructor
      · intro a' ha' heq
        subst heq
        exact h_not_in ha'
      · exact ih
    · change List.Nodup (if true then tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) [] else hd :: tl.foldr (fun x acc => if acc.contains x then acc else x :: acc) [])
      dsimp
      exact ih


theorem update_mem_strong {k : ScopedVar} {v : Int} {l : List (ScopedVar × Int)} {x : ScopedVar × Int}
  (h_in : x ∈ update l k v) : x = (k, v) ∨ x ∈ l := by
  induction l with
  | nil =>
    simp [update] at h_in
    left
    exact h_in
  | cons hd tl ih =>
    rcases hd with ⟨k', v'⟩
    simp [update] at h_in
    split at h_in
    · cases h_in with
      | head =>
        left
        rfl
      | tail _ h_in_tl =>
        right
        exact List.Mem.tail _ h_in_tl
    · cases h_in with
      | head =>
        right
        exact List.Mem.head _
      | tail _ h_in_tl =>
        rcases ih h_in_tl with h_eq | h_in_tl'
        · left; exact h_eq
        · right
          exact List.Mem.tail _ h_in_tl'

theorem relaxEdges_mem (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar))
  (changed : Bool) (x : ScopedVar × Int) :
  x ∈ (edges.foldl (fun (accD, accP, changed) e =>
      let d_u := lookup accD e.src
      let d_v := lookup accD e.dst
      if d_u + e.weight < d_v then
        (update accD e.dst (d_u + e.weight), updatePred accP e.dst e.src, true)
      else
        (accD, accP, changed)) (dist, pred, changed)).1 →
  x ∈ dist ∨ ∃ e ∈ edges, e.dst = x.1 := by
  induction edges generalizing dist pred changed with
  | nil =>
    simp
  | cons e edges ih =>
    intro h
    dsimp [List.foldl] at h
    let d_u := lookup dist e.src
    let d_v := lookup dist e.dst
    by_cases h_if : (d_u + e.weight < d_v)
    · rw [if_pos h_if] at h
      have ih_res := ih (update dist e.dst (d_u + e.weight)) (updatePred pred e.dst e.src) true h
      rcases ih_res with h_dist | ⟨e', he', he'_dst⟩
      · rcases update_mem_strong h_dist with h_eq | h_in_dist
        · right
          exists e
          have h_dst_eq : e.dst = x.1 := by
            have h1 : x.1 = e.dst := congrArg Prod.fst h_eq
            exact h1.symm
          exact ⟨List.Mem.head _, h_dst_eq⟩
        · left
          exact h_in_dist
      · right
        exists e'
        exact ⟨List.Mem.tail _ he', he'_dst⟩
    · rw [if_neg h_if] at h
      have ih_res := ih dist pred changed h
      rcases ih_res with h_dist | ⟨e', he', he'_dst⟩
      · left; exact h_dist
      · right; exists e'; exact ⟨List.Mem.tail _ he', he'_dst⟩

theorem buildEdges_cons (c : Constraint) (cs : List Constraint) :
  buildEdges (c :: cs) = buildEdges [c] ++ buildEdges cs := by
  exact buildEdges_append [c] cs

theorem mem_buildEdges_filter (cs : List Constraint) (e : Edge) :
  e ∈ buildEdges cs → ∃ c ∈ cs, e ∈ buildEdges [c] := by
  induction cs with
  | nil =>
    simp [buildEdges]
  | cons c cs ih =>
    intro h
    rw [buildEdges_cons] at h
    simp at h
    cases h with
    | inl h_in_c =>
      exists c
      constructor
      · exact List.Mem.head _
      · exact h_in_c
    | inr h_in_cs =>
      have ⟨c', hc', h_in_c'⟩ := ih h_in_cs
      exists c'
      constructor
      · exact List.Mem.tail _ hc'
      · exact h_in_c'

theorem buildEdges_subgraph_of_mem (cs : List Constraint) (c : Constraint) :
  c ∈ cs → ∀ e ∈ buildEdges [c], e ∈ buildEdges cs := by
  intro h e he
  induction cs with
  | nil => contradiction
  | cons hd tl ih =>
    rw [buildEdges_cons]
    simp
    cases h with
    | head _ =>
      left
      exact he
    | tail _ h_in_tl =>
      right
      exact ih h_in_tl

theorem satisfies_of_mem_filter (cs : List Constraint) (d : ScopedVar → Int) (c : Constraint)
  (h_sat : SatisfiesGraph d (buildEdges (cs.filter (fun c' => c'.v1.2 == c.v1.2))))
  (h_in : c ∈ cs) :
  SatisfiesGraph d (buildEdges [c]) := by
  intro e he
  apply h_sat
  apply buildEdges_subgraph_of_mem (cs.filter (fun c' => c'.v1.2 == c.v1.2)) c
  · rw [List.mem_filter]
    constructor
    · exact h_in
    · simp
  · exact he

theorem satisfies_all_scopes (cs : List Constraint) (d : ScopedVar → Int)
  (h_sat : ∀ c ∈ cs, SatisfiesGraph d (buildEdges [c])) :
  SatisfiesGraph d (buildEdges cs) := by
  intro e he
  have ⟨c, hc, he_c⟩ := mem_buildEdges_filter cs e he
  exact h_sat c hc e he_c

theorem relaxEdges_preserves_scope (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (changed : Bool) (s : Nat)
  (h_dist : ∀ x ∈ dist, x.1.2 = s)
  (h_edges : ∀ e ∈ edges, e.dst.2 = s) :
  ∀ x ∈ (relaxEdges edges dist pred).1, x.1.2 = s := by
  intro x hx
  unfold relaxEdges at hx
  have h_mem := relaxEdges_mem edges dist pred false x hx
  cases h_mem with
  | inl h_in_dist => exact h_dist x h_in_dist
  | inr h_in_edges =>
    rcases h_in_edges with ⟨e, he_mem, he_dst_eq⟩
    have he_s := h_edges e he_mem
    rw [he_dst_eq] at he_s
    exact he_s

theorem loop_preserves_scope (n : Nat) (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) (s : Nat)
  (h_dist : ∀ x ∈ dist, x.1.2 = s)
  (h_edges : ∀ e ∈ edges, e.dst.2 = s) :
  ∀ x ∈ (evaluateClause.loop edges n dist pred).1, x.1.2 = s := by
  induction n generalizing dist pred with
  | zero =>
    unfold evaluateClause.loop
    exact h_dist
  | succ n ih =>
    unfold evaluateClause.loop
    dsimp
    generalize h_relax : relaxEdges edges dist pred = relax_res
    match relax_res with
    | (dist', pred', changed) =>
      dsimp
      by_cases h_changed : changed = true
      · have h_not_changed : (!changed) = false := by simp [h_changed]
        rw [h_not_changed]
        dsimp
        apply ih
        have h_relax_dist : dist' = (relaxEdges edges dist pred).1 := by rw [h_relax]
        subst h_relax_dist
        exact relaxEdges_preserves_scope edges dist pred false s h_dist h_edges
      · have h_not_changed : (!changed) = true := by
          cases changed
          · rfl
          · contradiction
        rw [h_not_changed]
        dsimp
        have h_relax_dist : dist' = (relaxEdges edges dist pred).1 := by rw [h_relax]
        subst h_relax_dist
        exact relaxEdges_preserves_scope edges dist pred false s h_dist h_edges

theorem evaluateClause_preserves_scope (vars : List ScopedVar) (constraints : List Constraint) (dist : List (ScopedVar × Int)) (s : Nat)
  (h_vars : ∀ v ∈ vars, v.2 = s)
  (h_edges : ∀ e ∈ buildEdges constraints, e.dst.2 = s)
  (h_eval : evaluateClause vars constraints = Except.ok dist) :
  ∀ x ∈ dist, x.1.2 = s := by
  dsimp [evaluateClause] at h_eval
  split at h_eval
  · next h_n =>
    injection h_eval with h_eq
    rw [←h_eq]
    simp
  · next h_n =>
    revert h_eval
    generalize h1 : evaluateClause.loop (buildEdges constraints) (vars.length - 1) (List.map (fun v => (v, (0 : Int))) vars) [] = loop_res
    match loop_res with
    | (finalDist, finalPred) =>
      intro h_eval
      generalize h2 : relaxEdges (buildEdges constraints) finalDist finalPred = relax_res
      match relax_res with
      | (fst, cyclePred, hasCycle) =>
        split at h_eval
        · next h_not_hasCycle =>
          injection h_eval with h_eq
          rw [←h_eq]
          have h_scope_final : ∀ x ∈ finalDist, x.1.2 = s := by
            have h_loop_scope := loop_preserves_scope (vars.length - 1) (buildEdges constraints) (List.map (fun v => (v, (0 : Int))) vars) [] s
            have h_init : ∀ x ∈ List.map (fun v => (v, (0 : Int))) vars, x.1.2 = s := by
              intro x hx
              rcases List.mem_map.mp hx with ⟨v, hv, heq⟩
              rw [←heq]
              exact h_vars v hv
            have h_loop := h_loop_scope h_init h_edges
            rw [h1] at h_loop
            exact h_loop
          exact h_scope_final
        · next h_hasCycle =>
          split at h_eval
          · contradiction
          · contradiction

theorem extractConstraintsAux_v1_mem (s : Nat) (f : Formula) (c : Constraint)
  (h_in : c ∈ extractConstraintsAux s f) :
  c.v1 ∈ getFormulaVarsAux s f := by
  induction f generalizing s with
  | atom a =>
    cases a <;> simp [extractConstraintsAux, getFormulaVarsAux] at h_in ⊢
    · rcases h_in with rfl | rfl <;> simp
    · rcases h_in with rfl | rfl <;> simp
    · rcases h_in with rfl | rfl <;> simp
    · rcases h_in with rfl <;> simp
    · rcases h_in with rfl <;> simp
    · rcases h_in with rfl | rfl <;> simp
    · rcases h_in with rfl | rfl <;> simp
  | neg p ih =>
    exact ih s h_in
  | conj p q ih_p ih_q =>
    simp [extractConstraintsAux, getFormulaVarsAux] at h_in ⊢
    rcases h_in with h | h
    · left; exact ih_p s h
    · right; exact ih_q s h
  | disj p q ih_p ih_q =>
    simp [extractConstraintsAux, getFormulaVarsAux] at h_in ⊢
    rcases h_in with h | h
    · left; exact ih_p s h
    · right; exact ih_q s h
  | impl p q ih_p ih_q =>
    simp [extractConstraintsAux, getFormulaVarsAux] at h_in ⊢
    rcases h_in with h | h
    · left; exact ih_p s h
    · right; exact ih_q s h
  | univ n name p ih =>
    exact ih n h_in
  | comp n name p ih =>
    exact ih n h_in

theorem evaluateClausePartitioned_sound (f : Formula) (w : StratificationWitness)
  (h_eval : evaluateClausePartitioned (getFormulaVars f) (extractConstraintsAux 0 f) = StratificationResult.success w) :
  SatisfiesGraph (lookupWitness w) (buildEdges (extractConstraintsAux 0 f)) := by
  have h_vars_cons : ∀ s, (getFormulaVars f).filter (fun v => v.2 == s) = [] → (extractConstraintsAux 0 f).filter (fun c => c.v1.2 == s) = [] := by
    intro s h_vars
    unfold getFormulaVars at h_vars
    have h_orig : (getFormulaVarsAux 0 f).filter (fun v => v.2 == s) = [] := by
      rw [List.filter_eq_nil_iff] at h_vars ⊢
      intro x hx
      apply h_vars x
      rw [mem_nub]
      exact hx
    apply filter_scope_empty_vars_constraints f s 0 h_orig
  unfold evaluateClausePartitioned at h_eval
  apply satisfies_all_scopes
  intro c hc
  have h_scope_eq : c.v1.2 = c.v2.2 := extractConstraintsAux_scope_parity 0 f c hc
  let s := c.v1.2
  have hs_in : s ∈ nub ((getFormulaVars f).map (fun v => v.2)) := by
    rw [mem_nub]
    have h_in_vars : c.v1 ∈ getFormulaVarsAux 0 f := extractConstraintsAux_v1_mem 0 f c hc
    unfold getFormulaVars
    apply List.mem_map_of_mem; exact (mem_nub _ _).mpr h_in_vars
  have h_sat_s_full := evalScopes_sound
    (getFormulaVars f)
    (extractConstraintsAux 0 f)
    (nub ((getFormulaVars f).map (fun v => v.2)))
    []
    w
    h_eval
    h_vars_cons
    s
    hs_in
    (by intro s' _; simp)
    (nodup_nub _)
    (by
      intro s' dist' h_eval_scope
      apply evaluateClause_preserves_scope (getFormulaVars f |>.filter (fun v => v.2 == s')) (extractConstraintsAux 0 f |>.filter (fun c => c.v1.2 == s'))
      · intro v hv
        rw [List.mem_filter] at hv
        exact eq_of_beq hv.right
      · intro e he
        have ⟨c', hc', he_c'⟩ := mem_buildEdges_filter _ _ he
        simp [List.mem_filter] at hc'
        have hc'_scope := extractConstraintsAux_scope_parity 0 f c' hc'.left
        have he_scope := buildEdges_scope_preserve s' [c'] (by
          intro c'' hc''
          simp at hc''
          subst hc''
          exact ⟨hc'.right, by rw [←hc'_scope, hc'.right]⟩) e he_c'
        exact he_scope.right
      · exact h_eval_scope)
    (by
      intro c' hc'
      exact extractConstraintsAux_scope_parity 0 f c' hc')
  exact satisfies_of_mem_filter (extractConstraintsAux 0 f) _ c h_sat_s_full hc

theorem stratification_sound (f : Formula) (w : StratificationWitness)
  (h_eval : evaluateStratification f = StratificationResult.success w) :
  IsStratified f (lookupWitness w) := by
  exact stratified_of_satisfies 0 f (lookupWitness w) (evaluateClausePartitioned_sound f w (by exact h_eval))
