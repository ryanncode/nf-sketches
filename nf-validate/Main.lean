import NfValidate

import Init.Data.List.Basic

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"

-- Variables are represented as strings for the MVP
abbrev Var := String

-- Abstract Syntax Tree for first-order logic with membership and equality
inductive Formula where
  | eq : Var → Var → Formula               -- x = y
  | mem : Var → Var → Formula              -- x ∈ y
  | neg : Formula → Formula                -- ¬φ
  | conj : Formula → Formula → Formula     -- φ ∧ ψ
  | univ : Var → Formula → Formula         -- ∀x, φ
  deriving Repr, BEq

-- A constraint representing the required level difference between two variables
-- diff = level(v2) - level(v1)
structure Constraint where
  v1 : Var
  v2 : Var
  diff : Int
  deriving Repr, BEq

-- Traverse the AST to extract all stratification constraints
def extractConstraints : Formula → List Constraint
  | Formula.eq x y => [{ v1 := x, v2 := y, diff := 0 }]
  | Formula.mem x y => [{ v1 := x, v2 := y, diff := 1 }]
  | Formula.neg p => extractConstraints p
  | Formula.conj p q => extractConstraints p ++ extractConstraints q
  | Formula.univ _ p => extractConstraints p

-- A context mapping variables to their assigned integer levels
abbrev Context := List (Var × Int)

def lookup (ctx : Context) (v : Var) : Option Int :=
  match ctx with
  | [] => none
  | (x, l) :: xs => if x == v then some l else lookup xs v

-- Evaluate a constraint against the current typing context
-- Returns the updated context if stratifiable, or none if a contradiction is found
def applyConstraint (ctx : Context) (c : Constraint) : Option Context :=
  match lookup ctx c.v1, lookup ctx c.v2 with
  | some l1, some l2 =>
      if l2 - l1 == c.diff then some ctx else none
  | some l1, none => some ((c.v2, l1 + c.diff) :: ctx)
  | none, some l2 => some ((c.v1, l2 - c.diff) :: ctx)
  | none, none => some ((c.v1, 0) :: (c.v2, c.diff) :: ctx)

-- Iterate through all constraints to build the stratification assignment
-- Note: This is a linear pass. Complete implementations require cycle detection.
def resolveConstraints (cs : List Constraint) (ctx : Context) : Option Context :=
  match cs with
  | [] => some ctx
  | c :: rest =>
      match applyConstraint ctx c with
      | none => none
      | some newCtx => resolveConstraints rest newCtx

-- Main execution function
def isStratifiable (f : Formula) : Bool :=
  let constraints := extractConstraints f
  match resolveConstraints constraints [] with
  | some _ => true
  | none => false
