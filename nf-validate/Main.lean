import NfValidate

import Init.Data.List.Basic

abbrev Var := String

inductive Formula where
  | eq : Var → Var → Formula
  | mem : Var → Var → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | univ : Var → Formula → Formula
  deriving Repr, BEq

structure Constraint where
  v1 : Var
  v2 : Var
  diff : Int
  deriving Repr, BEq

def extractConstraints : Formula → List Constraint
  | Formula.eq x y => [{ v1 := x, v2 := y, diff := 0 }]
  | Formula.mem x y => [{ v1 := x, v2 := y, diff := 1 }]
  | Formula.neg p => extractConstraints p
  | Formula.conj p q => extractConstraints p ++ extractConstraints q
  | Formula.univ _ p => extractConstraints p

abbrev Context := List (Var × Int)

def lookup (ctx : Context) (v : Var) : Option Int :=
  match ctx with
  | [] => none
  | (x, l) :: xs => if x == v then some l else lookup xs v

def applyConstraint (ctx : Context) (c : Constraint) : Option Context :=
  match lookup ctx c.v1, lookup ctx c.v2 with
  | some l1, some l2 =>
      if l2 - l1 == c.diff then some ctx else none
  | some l1, none => some ((c.v2, l1 + c.diff) :: ctx)
  | none, some l2 => some ((c.v1, l2 - c.diff) :: ctx)
  | none, none => some ((c.v1, 0) :: (c.v2, c.diff) :: ctx)

def resolveConstraints (cs : List Constraint) (ctx : Context) : Option Context :=
  match cs with
  | [] => some ctx
  | c :: rest =>
      match applyConstraint ctx c with
      | none => none
      | some newCtx => resolveConstraints rest newCtx

def isStratifiable (f : Formula) : Bool :=
  match resolveConstraints (extractConstraints f) [] with
  | some _ => true
  | none => false

-- IO and Parsing Components

def buildConjunction (atoms : List Formula) : Option Formula :=
  match atoms with
  | [] => none
  | [x] => some x
  | x :: xs =>
      match buildConjunction xs with
      | some rest => some (Formula.conj x rest)
      | none => none

def parseAtomic (s : String) : Option Formula :=
  let parts := s.splitOn " "
  match parts with
  | [x, "=", y] => some (Formula.eq x y)
  | [x, "e", y] => some (Formula.mem x y)
  | _ => none

partial def readFormulas (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (acc : List Formula) : IO (List Formula) := do
  stdout.putStr "> "
  stdout.flush
  let line ← stdin.getLine
  let input := line.trim
  if input == "done" then
    return acc
  else
    match parseAtomic input with
    | some f => readFormulas stdin stdout (acc ++ [f])
    | none =>
        stdout.putStrLn "Invalid format. Use the exact syntax 'x = y' or 'x e y'."
        readFormulas stdin stdout acc

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "=== NF Stratification Validator MVP ==="
  stdout.putStrLn "Enter atomic formulas to build a conjunction."
  stdout.putStrLn "Accepted syntax: 'x = y' for equality, 'x e y' for membership."
  stdout.putStrLn "Type 'done' to evaluate the combined formula."

  let atoms ← readFormulas stdin stdout []
  match buildConjunction atoms with
  | none => stdout.putStrLn "Execution terminated. No formulas were entered."
  | some f =>
      stdout.putStrLn "\nEvaluating constraint graph..."
      let strat := isStratifiable f
      if strat then
        stdout.putStrLn "Result: The formula is stratifiable."
      else
        stdout.putStrLn "Result: Not stratifiable. A typing contradiction or cycle was detected."
