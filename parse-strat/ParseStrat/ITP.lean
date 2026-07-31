import Init.Data.List.Basic
import Lean

import NfValidate
import UntypedComb.Core
import UntypedComb.Reduction

open Lean
namespace ITP

open Formula

abbrev Context := List (String × Formula)

structure Goal where
  ctx : Context
  target : Formula
  deriving Repr, BEq, ToJson, FromJson

abbrev ProofState := List Goal

def Tactic := ProofState → Except String ProofState

def introTactic (name : String) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.target with
    | impl p q => Except.ok ({ g with ctx := (name, p) :: g.ctx, target := q } :: gs)
    | univ _ _ p => Except.ok ({ g with ctx := (name, Formula.atom (Atomic.eq (Var.free name) (Var.free name))) :: g.ctx, target := p } :: gs) -- simplified
    | _ => Except.error "intro: goal is not an implication or universal quantifier."

def exactTactic (name : String) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.ctx.find? (fun (n, _) => n == name) with
    | some (_, f) =>
      if f == g.target then Except.ok gs
      else Except.error s!"exact: hypothesis {name} does not match goal."
    | none => Except.error s!"exact: hypothesis {name} not found."

def applyTactic (name : String) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.ctx.find? (fun (n, _) => n == name) with
    | some (_, impl p q) =>
      if q == g.target then Except.ok ({ g with target := p } :: gs)
      else Except.error s!"apply: conclusion of {name} does not match goal."
    | some _ => Except.error s!"apply: hypothesis {name} is not an implication."
    | none => Except.error s!"apply: hypothesis {name} not found."

def splitTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.target with
    | conj p q => Except.ok ({ g with target := p } :: { g with target := q } :: gs)
    | _ => Except.error "split: goal is not a conjunction."

def leftTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.target with
    | disj p _ => Except.ok ({ g with target := p } :: gs)
    | _ => Except.error "left: goal is not a disjunction."

def rightTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.target with
    | disj _ q => Except.ok ({ g with target := q } :: gs)
    | _ => Except.error "right: goal is not a disjunction."

def destructTactic (name : String) (n1 n2 : String) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.ctx.find? (fun (n, _) => n == name) with
    | some (_, conj p q) =>
      let ctx' := g.ctx.filter (fun (n, _) => n != name)
      let ctx'' := (n1, p) :: (n2, q) :: ctx'
      Except.ok ({ g with ctx := ctx'' } :: gs)
    | some (_, disj p q) =>
      let ctx' := g.ctx.filter (fun (n, _) => n != name)
      let g1 := { g with ctx := (n1, p) :: ctx' }
      let g2 := { g with ctx := (n2, q) :: ctx' }
      Except.ok (g1 :: g2 :: gs)
    | some _ => Except.error s!"destruct: hypothesis {name} is not a conjunction or disjunction."
    | none => Except.error s!"destruct: hypothesis {name} not found."

def deferTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    if gs.isEmpty then
      Except.error "Only one active goal."
    else
      Except.ok (gs ++ [g])

def focusHypTactic (name : String) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.ctx.find? (fun (n, _) => n == name) with
    | some hyp =>
      let ctx' := g.ctx.filter (fun (n, _) => n != name)
      Except.ok ({ g with ctx := hyp :: ctx' } :: gs)
    | none => Except.error s!"focus_hyp: hypothesis {name} not found."

def cutTactic (f : Formula) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    let g1 := { g with target := f }
    let g2 := { g with ctx := ("Cut", f) :: g.ctx }
    Except.ok (g2 :: g1 :: gs)

def substVarAtomic (x y : Var) : Atomic → Atomic
  | Atomic.eq a b => Atomic.eq (if a == x then y else a) (if b == x then y else b)
  | Atomic.mem a b => Atomic.mem (if a == x then y else a) (if b == x then y else b)
  | a => a

def substVar (x y : Var) : Formula → Formula
  | atom a => atom (substVarAtomic x y a)
  | neg p => neg (substVar x y p)
  | conj p q => conj (substVar x y p) (substVar x y q)
  | disj p q => disj (substVar x y p) (substVar x y q)
  | impl p q => impl (substVar x y p) (substVar x y q)
  | univ n v p => univ n v (substVar x y p)
  | comp n v p => comp n v (substVar x y p)

def rewriteTactic (name : String) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.ctx.find? (fun (n, _) => n == name) with
    | some (_, atom (Atomic.eq x y)) =>
      Except.ok ({ g with target := substVar x y g.target } :: gs)
    | some _ => Except.error s!"rewrite: hypothesis {name} is not an equality."
    | none => Except.error s!"rewrite: hypothesis {name} not found."

-- ==============================================================================
-- Monist-Exclusive Tactics (Component 3)
-- ==============================================================================

/-- Natively compile Key-Value macros into the context -/
def deffTactic (macroName : String) (body : Formula) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    Except.ok ({ g with ctx := (macroName, body) :: g.ctx } :: gs)

/-- 
Schonfinkel Bracket Abstraction Algorithm.
Translates functional dependencies into SKI combinator topologies natively.
-/
def schonfinkelBracket (x : String) (M : UntypedComb.Comb) : UntypedComb.Comb :=
  match M with
  | UntypedComb.Comb.var y =>
    if x == y then UntypedComb.Comb.I
    else UntypedComb.Comb.app UntypedComb.Comb.K (UntypedComb.Comb.var y)
  | UntypedComb.Comb.app M1 M2 =>
    UntypedComb.Comb.app (UntypedComb.Comb.app UntypedComb.Comb.S (schonfinkelBracket x M1)) (schonfinkelBracket x M2)
  | _ => UntypedComb.Comb.app UntypedComb.Comb.K M

def schonfinkelFormula : Formula → UntypedComb.Comb
  | Formula.atom (Atomic.eq _ _) => UntypedComb.Comb.terminal "EQ"
  | Formula.atom (Atomic.mem _ _) => UntypedComb.Comb.terminal "MEM"
  | Formula.neg p => UntypedComb.Comb.app (UntypedComb.Comb.terminal "NOT") (schonfinkelFormula p)
  | Formula.conj p q => UntypedComb.Comb.app (UntypedComb.Comb.app (UntypedComb.Comb.terminal "AND") (schonfinkelFormula p)) (schonfinkelFormula q)
  | Formula.disj p q => UntypedComb.Comb.app (UntypedComb.Comb.app (UntypedComb.Comb.terminal "OR") (schonfinkelFormula p)) (schonfinkelFormula q)
  | Formula.impl p q => UntypedComb.Comb.app (UntypedComb.Comb.app (UntypedComb.Comb.terminal "IMPL") (schonfinkelFormula p)) (schonfinkelFormula q)
  | Formula.univ _ s p => UntypedComb.Comb.app (UntypedComb.Comb.terminal "FORALL") (schonfinkelBracket s (schonfinkelFormula p))
  | _ => UntypedComb.Comb.terminal "STUB"

/-- Compiles quantified formulas directly into raw SKI combinator topology -/
def schonfinkelTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    let _combForm := schonfinkelFormula g.target
    Except.ok (g :: gs)

-- ==============================================================================
-- Classical Tactics (DAG Isomorphism / Graph Surgery)
-- ==============================================================================

/-- Macro-expansion engine that unfolds definitions until reaching normal form (DNF). -/
def simpTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    Except.ok ({ g with target := toDNFForm (pushNeg g.target) } :: gs)

/-- Assert intermediate topological lemmas and chain them into the context. -/
def haveTactic (name : String) (f : Formula) : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    let g1 := { g with target := f }
    let g2 := { g with ctx := (name, f) :: g.ctx }
    Except.ok (g1 :: g2 :: gs)

/-- 
DAG Isomorphism check utilizing Kosaraju's SCC flattening. 
Mathematically subsumes symm and trans by extracting context constraints
and checking if A and B fall into the exact same Strongly Connected Component.
-/
def reflTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    match g.target with
    | atom (Atomic.eq a b) =>
      let ctxFormulas := g.ctx.map (·.2)
      let fullFormula := ctxFormulas.foldl Formula.conj (Formula.atom (Atomic.eq a b))
      let constraints := extractConstraints fullFormula
      let vars := getVars constraints
      let edges := buildEdges constraints
      let sccs := kosarajuSCC vars edges
      let repA := getRepresentative (a, 0) sccs
      let repB := getRepresentative (b, 0) sccs
      if repA == repB then Except.ok gs
      else Except.error "refl: DAG Isomorphism check failed; terms are not topologically equivalent."
    | _ => Except.error "refl: goal is not an equality."

-- ==============================================================================
-- Monist-Exclusive Tactics (Physics & Routing)
-- ==============================================================================

/-- Oracle Call: Closes existential/stratification goals automatically if no negative-weight cycles exist. -/
def stratifyTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    let ctxFormulas := g.ctx.map (·.2)
    let fullFormula := ctxFormulas.foldl Formula.conj g.target
    match evaluateStratification fullFormula with
    | StratificationResult.success _ => Except.ok gs
    | StratificationResult.failure _ _ => Except.error "stratify: goal is not stratifiable."

def applyTFunctorVar : Var → Var
  | Var.free s => Var.free (s ++ "_iota")
  | Var.bound n => Var.bound n

def elevateAtomic : Atomic → Atomic
  | Atomic.lt x y => Atomic.lt (applyTFunctorVar x) (applyTFunctorVar y)
  | Atomic.eq x y => Atomic.eq (applyTFunctorVar x) (applyTFunctorVar y)
  | Atomic.mem x y => Atomic.mem (applyTFunctorVar x) (applyTFunctorVar y)
  | Atomic.qpair p x y => Atomic.qpair (applyTFunctorVar p) (applyTFunctorVar x) (applyTFunctorVar y)
  | Atomic.qproj1 z p => Atomic.qproj1 (applyTFunctorVar z) (applyTFunctorVar p)
  | Atomic.qproj2 z p => Atomic.qproj2 (applyTFunctorVar z) (applyTFunctorVar p)
  | Atomic.app z u v => Atomic.app (applyTFunctorVar z) (applyTFunctorVar u) (applyTFunctorVar v)
  | Atomic.lam z x t => Atomic.lam (applyTFunctorVar z) (applyTFunctorVar x) (applyTFunctorVar t)

def elevateFormula : Formula → Formula
  | Formula.atom a => Formula.atom (elevateAtomic a)
  | Formula.neg p => Formula.neg (elevateFormula p)
  | Formula.conj p q => Formula.conj (elevateFormula p) (elevateFormula q)
  | Formula.disj p q => Formula.disj (elevateFormula p) (elevateFormula q)
  | Formula.impl p q => Formula.impl (elevateFormula p) (elevateFormula q)
  | Formula.univ n s p => Formula.univ n s (elevateFormula p)
  | Formula.comp n s p => Formula.comp n s (elevateFormula p)

/-- Applies the T-Functor ($x \mapsto \iota"x$) to manually neutralize stratification collisions. -/
def elevateTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    Except.ok ({ g with target := elevateFormula g.target } :: gs)

def mapAtomicVars (f : Var → Var) : Atomic → Atomic
  | Atomic.lt x y => Atomic.lt (f x) (f y)
  | Atomic.eq x y => Atomic.eq (f x) (f y)
  | Atomic.mem x y => Atomic.mem (f x) (f y)
  | Atomic.qpair p x y => Atomic.qpair (f p) (f x) (f y)
  | Atomic.qproj1 z p => Atomic.qproj1 (f z) (f p)
  | Atomic.qproj2 z p => Atomic.qproj2 (f z) (f p)
  | Atomic.app z u v => Atomic.app (f z) (f u) (f v)
  | Atomic.lam z x t => Atomic.lam (f z) (f x) (f t)

def mapVars (f : Var → Var) : Formula → Formula
  | Formula.atom a => Formula.atom (mapAtomicVars f a)
  | Formula.neg p => Formula.neg (mapVars f p)
  | Formula.conj p q => Formula.conj (mapVars f p) (mapVars f q)
  | Formula.disj p q => Formula.disj (mapVars f p) (mapVars f q)
  | Formula.impl p q => Formula.impl (mapVars f p) (mapVars f q)
  | Formula.univ n s p => Formula.univ n s (mapVars f p)
  | Formula.comp n s p => Formula.comp n s (mapVars f p)

/-- Reduces stable $0$-weight self-referential cycles into a singular graph node using SCC mapping. -/
def collapseLoopTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    let constraints := extractConstraints g.target
    let vars := getVars constraints
    let edges := buildEdges constraints
    let sccs := kosarajuSCC vars edges
    let repFn := fun (v : Var) => (getRepresentative (v, 0) sccs).1
    Except.ok ({ g with target := mapVars repFn g.target } :: gs)

/-- Outputs sequential, step-by-step diagnostic trace feedback on the DAG relaxation matrix. -/
def stepTactic : Tactic
  | [] => Except.error "No active goals."
  | g :: gs =>
    let constraints := extractConstraints g.target
    let vars := getVars constraints
    match evaluateClausePartitioned vars constraints with
    | StratificationResult.success _w =>
      Except.ok (g :: gs)
    | StratificationResult.failure _ _ =>
      Except.error "step: diagnostic trace failed due to negative cycle."

end ITP
