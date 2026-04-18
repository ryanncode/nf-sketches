import NfValidate

/-!
# Bowler's Acyclic Translation Algorithm

This module implements the core translation mechanism for evaluating the theorem
that "stratified = acyclic" under weak stratification. By mapping arbitrary
stratified comprehension formulas into finite axiomatizations, it establishes
the structural prerequisites necessary to replace $O(V \cdot E)$ cycle detection
with an $O(V+E)$ Directed Acyclic Graph (DAG) topological sort.

## Topological Constraints
1. No path > 1 between $u$ and $v$.
2. All occurrences of $x$ are free, or bound by the same exact quantifier.
3. No atomic formula occurs more than once.
4. Propositional connectives are restricted to negation and disjunction (with
   conjunction and implication mapped via definitional expansion).
-/

namespace Bowler

-- Generates a unique fresh variable for diversification
def freshVar (prefixName : String) (seed : Nat) : Var :=
  Var.free s!"{prefixName}_{seed}"

-- 1. Defitional Expansion
-- Ensure all formulas are reduced to strictly use `neg` and `disj` logic.
-- Conjunction and implication are mapped via De Morgan's and material implication.
def expandConnectives : Formula → Formula
  | Formula.conj p q => Formula.neg (Formula.disj (Formula.neg (expandConnectives p)) (Formula.neg (expandConnectives q)))
  | Formula.impl p q => Formula.disj (Formula.neg (expandConnectives p)) (expandConnectives q)
  | Formula.neg p => Formula.neg (expandConnectives p)
  | Formula.disj p q => Formula.disj (expandConnectives p) (expandConnectives q)
  | Formula.univ n x p => Formula.univ n x (expandConnectives p)
  | Formula.comp n x p => Formula.comp n x (expandConnectives p)
  | p => p

-- 2. Quine Ordered Pairs Implementation
-- Replaces Kuratowski pairs with Quine ordered pairs to maintain homogeneous typing.
-- A Quine ordered pair `\langle x, y \rangle` exists at the exact same type level as `x` and `y`.
-- Here we synthesize the structure for `Pair(p)` and `Proj(z, p)`.
-- Under NF, a Quine ordered pair is typically defined using a specific set-theoretic construction.
-- For the acyclic translation, we need to express "p is a Quine ordered pair of x and y".
-- As a foundational logic engine, we need `isPair(p)` and `isProj(z, p)` to map to valid acyclic AST components.
def isPair (scope : Nat) (p x y : Var) : Formula :=
  Formula.atom (Atomic.qpair p x y)

def isProj1 (scope : Nat) (z p : Var) : Formula :=
  Formula.atom (Atomic.qproj1 z p)

def isProj2 (scope : Nat) (z p : Var) : Formula :=
  Formula.atom (Atomic.qproj2 z p)

-- 3. The Equality Relation [=] Synthesis
-- Synthesized acyclically as {p | Pair(p) \wedge (\exists x.(\forall z.Proj(z,p) \rightarrow x=z))}
def acyclicEq (scope : Nat) (p x y z : Var) : Formula :=
  -- Pair(p) \wedge \exists x. \forall z. (Proj1(z, p) \rightarrow x = z)
  -- Note: A complete acyclic representation requires mapping both projections to avoid cycles
  let proj_impl := Formula.impl (isProj1 scope z p) (Formula.atom (Atomic.eq x z))
  let forall_z := Formula.univ scope "z" proj_impl
  let exists_x := Formula.neg (Formula.univ (scope + 1) "x" (Formula.neg forall_z))
  Formula.conj (isPair scope p x y) exists_x

-- 4. Universal Set (V) Map
-- V = {x | (\exists y. x = y)}
def acyclicV (scope : Nat) (x y : Var) : Formula :=
  let x_eq_y := Formula.atom (Atomic.eq x y)
  let exists_y := Formula.neg (Formula.univ scope "y" (Formula.neg x_eq_y))
  Formula.comp (scope + 1) "x" exists_y

-- 5. Boolean Union Map (a \cup b)
-- {x | x \in a \vee x \in b}
def acyclicUnion (scope : Nat) (x a b : Var) : Formula :=
  let x_in_a := Formula.atom (Atomic.mem x a)
  let x_in_b := Formula.atom (Atomic.mem x b)
  Formula.comp scope "x" (Formula.disj x_in_a x_in_b)

-- 6. Acyclic Graph Flattening
-- Identifies Harmless Cycles via O(V+E) Kosaraju's SCC on 0-weight edges.

def getNeighbors (edges : List Edge) (u : ScopedVar) : List ScopedVar :=
  edges.filter (fun e => e.src == u && e.weight == 0) |>.map (fun e => e.dst)

def getReverseNeighbors (edges : List Edge) (u : ScopedVar) : List ScopedVar :=
  edges.filter (fun e => e.dst == u && e.weight == 0) |>.map (fun e => e.src)

partial def dfsForward (edges : List Edge) (u : ScopedVar) (visited : List ScopedVar) (stack : List ScopedVar) : List ScopedVar × List ScopedVar :=
  if visited.contains u then (visited, stack)
  else
    let neighbors := getNeighbors edges u
    let (v_after, s_after) := neighbors.foldl (fun (v_acc, s_acc) n =>
      dfsForward edges n v_acc s_acc
    ) (u :: visited, stack)
    (v_after, u :: s_after)

partial def dfsBackward (edges : List Edge) (u : ScopedVar) (visited : List ScopedVar) (component : List ScopedVar) : List ScopedVar × List ScopedVar :=
  if visited.contains u then (visited, component)
  else
    let neighbors := getReverseNeighbors edges u
    let (v_after, c_after) := neighbors.foldl (fun (v_acc, c_acc) n =>
      dfsBackward edges n v_acc c_acc
    ) (u :: visited, u :: component)
    (v_after, c_after)

def findSCCs (vars : List ScopedVar) (edges : List Edge) : List (List ScopedVar) :=
  let (_, stack) := vars.foldl (fun (v_acc, s_acc) v =>
    dfsForward edges v v_acc s_acc
  ) ([], [])

  let (_, sccs) := stack.foldl (fun (v_acc, comps) v =>
    if v_acc.contains v then (v_acc, comps)
    else
      let (v_after, comp) := dfsBackward edges v v_acc []
      (v_after, comp :: comps)
  ) ([], [])
  sccs.filter (fun c => c.length > 1)

def expandVar (sccs : List (List ScopedVar)) (v : Var) (scope : Nat) : Option Var :=
  let sv := (v, scope)
  let matchingSCC := sccs.find? (fun c => c.contains sv)
  match matchingSCC with
  | some (canonical :: _) => if canonical.1 != v then some canonical.1 else none
  | _ => none

def injectProjection (scope : Nat) (p : Var) (seed : Nat) (inner : Var → Formula) : Formula :=
  let v_fresh := freshVar "fused" seed
  let proj := isProj1 scope v_fresh p
  let inner_f := inner v_fresh
  -- \exists v_fresh. (proj \land inner)
  -- \equiv \neg \forall v_fresh (\neg proj \lor \neg inner)
  let or_expr := Formula.disj (Formula.neg proj) (Formula.neg inner_f)
  Formula.neg (Formula.univ (scope + 1) s!"fused_{seed}" or_expr)

def wrapProj (scope : Nat) (seed : Nat) (v : Var) (ev : Option Var) : (Var × Nat × (Formula → Formula)) :=
  match ev with
  | none => (v, seed, id)
  | some pv =>
      let fv := freshVar "fused" seed
      (fv, seed + 1, fun inner => injectProjection scope pv seed (fun _ => inner))

def flattenGraphAux (sccs : List (List ScopedVar)) : Nat → Nat → Formula → Formula × Nat
  | scope, seed, Formula.atom (Atomic.eq x y) =>
      let (rx, s1, wx) := wrapProj scope seed x (expandVar sccs x scope)
      let (ry, s2, wy) := wrapProj scope s1 y (expandVar sccs y scope)
      (wx (wy (Formula.atom (Atomic.eq rx ry))), s2)
  | scope, seed, Formula.atom (Atomic.mem x y) =>
      let (rx, s1, wx) := wrapProj scope seed x (expandVar sccs x scope)
      let (ry, s2, wy) := wrapProj scope s1 y (expandVar sccs y scope)
      (wx (wy (Formula.atom (Atomic.mem rx ry))), s2)
  | scope, seed, Formula.atom (Atomic.qpair p x y) =>
      let (rp, s1, wp) := wrapProj scope seed p (expandVar sccs p scope)
      let (rx, s2, wx) := wrapProj scope s1 x (expandVar sccs x scope)
      let (ry, s3, wy) := wrapProj scope s2 y (expandVar sccs y scope)
      (wp (wx (wy (Formula.atom (Atomic.qpair rp rx ry)))), s3)
  | scope, seed, Formula.atom (Atomic.qproj1 z p) =>
      let (rz, s1, wz) := wrapProj scope seed z (expandVar sccs z scope)
      let (rp, s2, wp) := wrapProj scope s1 p (expandVar sccs p scope)
      (wz (wp (Formula.atom (Atomic.qproj1 rz rp))), s2)
  | scope, seed, Formula.atom (Atomic.qproj2 z p) =>
      let (rz, s1, wz) := wrapProj scope seed z (expandVar sccs z scope)
      let (rp, s2, wp) := wrapProj scope s1 p (expandVar sccs p scope)
      (wz (wp (Formula.atom (Atomic.qproj2 rz rp))), s2)
  | scope, seed, Formula.neg p =>
      let (p', s') := flattenGraphAux sccs scope seed p
      (Formula.neg p', s')
  | scope, seed, Formula.conj p q =>
      let (p', s1) := flattenGraphAux sccs scope seed p
      let (q', s2) := flattenGraphAux sccs scope s1 q
      (Formula.conj p' q', s2)
  | scope, seed, Formula.disj p q =>
      let (p', s1) := flattenGraphAux sccs scope seed p
      let (q', s2) := flattenGraphAux sccs scope s1 q
      (Formula.disj p' q', s2)
  | scope, seed, Formula.impl p q =>
      let (p', s1) := flattenGraphAux sccs scope seed p
      let (q', s2) := flattenGraphAux sccs scope s1 q
      (Formula.impl p' q', s2)
  | scope, seed, Formula.univ n x p =>
      let (p', s') := flattenGraphAux sccs n seed p
      (Formula.univ n x p', s')
  | scope, seed, Formula.comp n x p =>
      let (p', s') := flattenGraphAux sccs n seed p
      (Formula.comp n x p', s')

def flattenGraph (f : Formula) : Formula :=
  let constraints := extractConstraints f
  let edges := buildEdges constraints
  let vars := getFormulaVars f
  let sccs := findSCCs vars edges
  (flattenGraphAux sccs 0 0 f).1

end Bowler
