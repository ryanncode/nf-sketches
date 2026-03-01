import NfValidate.FintypeGraph

variable {V : Type} [DecidableEq V]

-- 1. Define a recursive function cycleWeightSum on an unindexed List Edge that calculates the total weight.
def cycleWeightSum (edges : List (GenericEdge V)) : Int :=
  match edges with
  | [] => 0
  | e :: es => e.weight + cycleWeightSum es

inductive EdgeChain : List (GenericEdge V) → V → V → Prop where
  | nil (u : V) : EdgeChain [] u u
  | cons (e : GenericEdge V) {es : List (GenericEdge V)} {w v : V} (heq : e.dst = w) (h : EdgeChain es w v) : EdgeChain (e :: es) e.src v

-- 2. Prove a lemma telescoping_cycle_sum that sums the inequalities M(dst) ≤ M(src) + weight over a valid edge chain.
lemma telescoping_chain_sum (M : V → Int) (edges : List (GenericEdge V)) (u v : V) (h : EdgeChain edges u v) :
  (M v - M u) = (edges.map (fun e => M e.dst - M e.src)).sum := by
  induction h with
  | nil u => simp
  | cons e heq h_chain ih =>
    simp
    rw [← ih]
    subst heq
    omega

lemma telescoping_cycle_sum (M : V → Int) (edges : List (GenericEdge V)) (u : V) (h : EdgeChain edges u u) :
  0 = (edges.map (fun e => M e.dst - M e.src)).sum := by
  have h_chain := telescoping_chain_sum M edges u u h
  omega

lemma cycleWeightSum_append (l1 l2 : List (GenericEdge V)) :
  cycleWeightSum (l1 ++ l2) = cycleWeightSum l1 + cycleWeightSum l2 := by
  induction l1 with
  | nil => simp [cycleWeightSum]
  | cons e es ih =>
    simp [cycleWeightSum]
    rw [ih]
    omega

lemma sum_diff_ge_weight_sum (M : V → Int) (edges : List (GenericEdge V))
  (h_parent : ∀ e ∈ edges, M e.dst ≥ M e.src + e.weight) :
  (edges.map (fun e => M e.dst - M e.src)).sum ≥ cycleWeightSum edges := by
  induction edges with
  | nil => simp [cycleWeightSum]
  | cons e es ih =>
    simp [cycleWeightSum]
    have he : M e.dst ≥ M e.src + e.weight := h_parent e (List.Mem.head es)
    have hes : (es.map (fun e => M e.dst - M e.src)).sum ≥ cycleWeightSum es :=
      ih (fun e' he' => h_parent e' (List.Mem.tail e he'))
    omega

-- 3. Strict Inequality Contradiction
-- If the edges form a cycle in the parent graph, we have M(dst) ≥ M(src) + weight for all parent edges.
-- The strict edge triggering the update has M(dst) > M(src) + weight.
lemma cycleWeightSum_negative_of_strict_ineq (M : V → Int) (pref suff : List (GenericEdge V)) (strict_e : GenericEdge V) (u : V)
  (h_chain : EdgeChain (pref ++ strict_e :: suff) u u)
  (h_parent_pref : ∀ e ∈ pref, M e.dst ≥ M e.src + e.weight)
  (h_parent_suff : ∀ e ∈ suff, M e.dst ≥ M e.src + e.weight)
  (h_strict : M strict_e.dst > M strict_e.src + strict_e.weight) :
  cycleWeightSum (pref ++ strict_e :: suff) < 0 := by
  have h_tele := telescoping_cycle_sum M (pref ++ strict_e :: suff) u h_chain
  rw [List.map_append, List.sum_append, List.map_cons, List.sum_cons] at h_tele

  have h_pref : (pref.map (fun e => M e.dst - M e.src)).sum ≥ cycleWeightSum pref :=
    sum_diff_ge_weight_sum M pref h_parent_pref

  have h_suff : (suff.map (fun e => M e.dst - M e.src)).sum ≥ cycleWeightSum suff :=
    sum_diff_ge_weight_sum M suff h_parent_suff

  rw [cycleWeightSum_append, cycleWeightSum]

  omega
