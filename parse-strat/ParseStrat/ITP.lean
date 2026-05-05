import Init.Data.List.Basic
import Lean

import NfValidate

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

end ITP
