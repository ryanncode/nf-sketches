import NfValidate

import Init.Data.List.Basic
import Init.System.IO

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

structure Edge where
  src : Var
  dst : Var
  weight : Int
  deriving Repr, BEq

def buildEdges : List Constraint → List Edge
  | [] => []
  | c :: cs =>
      { src := c.v1, dst := c.v2, weight := c.diff } ::
      { src := c.v2, dst := c.v1, weight := -c.diff } ::
      buildEdges cs

def getVarsAux : List Constraint → List Var
  | [] => []
  | c :: cs => c.v1 :: c.v2 :: getVarsAux cs

partial def nub : List Var → List Var
  | [] => []
  | x :: xs => x :: nub (xs.filter (fun y => y != x))

def getVars (cs : List Constraint) : List Var :=
  nub (getVarsAux cs)

def lookup (l : List (Var × Int)) (k : Var) : Int :=
  match l with
  | [] => 0
  | (k', v) :: xs => if k == k' then v else lookup xs k

def update (l : List (Var × Int)) (k : Var) (v : Int) : List (Var × Int) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: xs => if k == k' then (k, v) :: xs else (k', v') :: update xs k v

def lookupPred (l : List (Var × Var)) (k : Var) : Option Var :=
  match l with
  | [] => none
  | (k', v) :: xs => if k == k' then some v else lookupPred xs k

def updatePred (l : List (Var × Var)) (k : Var) (v : Var) : List (Var × Var) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: xs => if k == k' then (k, v) :: xs else (k', v') :: updatePred xs k v

def relaxEdges (edges : List Edge) (dist : List (Var × Int)) (pred : List (Var × Var)) :
    List (Var × Int) × List (Var × Var) × Bool :=
  edges.foldl (fun (accD, accP, changed) e =>
    let du := lookup accD e.src
    let dv := lookup accD e.dst
    if du + e.weight < dv then
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)

partial def getCycleForward (pred : List (Var × Var)) (start : Var) (n : Nat) : List Var :=
  let rec goUp (curr : Var) (steps : Nat) : Var :=
    if steps == 0 then curr
    else match lookupPred pred curr with
         | some p => goUp p (steps - 1)
         | none => curr
  let cycleStart := goUp start n

  let rec collect (curr : Var) (acc : List Var) : List Var :=
    if acc.contains curr then curr :: acc
    else match lookupPred pred curr with
         | some p => collect p (curr :: acc)
         | none => curr :: acc

  collect cycleStart []

inductive StratificationResult where
  | success (witness : List (Var × Int))
  | failure (cycle : List Var) (edges : List Edge)

partial def evaluateStratification (f : Formula) : StratificationResult :=
  let constraints := extractConstraints f
  let vars := getVars constraints
  let edges := buildEdges constraints
  let n := vars.length

  let initialDist : List (Var × Int) := vars.map (fun v => (v, (0 : Int)))
  let initialPred : List (Var × Var) := []

  let rec loop (i : Nat) (d : List (Var × Int)) (p : List (Var × Var)) :=
    if i == 0 then (d, p)
    else
      let (d', p', changed) := relaxEdges edges d p
      if not changed then (d', p') else loop (i - 1) d' p'

  let (finalDist, finalPred) := loop (n - 1) initialDist initialPred

  let (_, _, hasCycle) := relaxEdges edges finalDist finalPred
  if not hasCycle then
    StratificationResult.success finalDist
  else
    let conflictNode := edges.findSome? (fun e =>
      let du := lookup finalDist e.src
      let dv := lookup finalDist e.dst
      if du + e.weight < dv then some e.dst else none
    )
    match conflictNode with
    | some node => StratificationResult.failure (getCycleForward finalPred node n) edges
    | none => StratificationResult.failure [] edges

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

def formatWitness (w : List (Var × Int)) : String :=
  let pairs := w.map (fun (v, l) => s!"{v} : {l}")
  "{" ++ String.intercalate ", " pairs ++ "}"

-- Helper to convert a list of variables into pairs of adjacent nodes
def cycleToPairs (c : List Var) : List (Var × Var) :=
  match c with
  | [] => []
  | _ :: [] => []
  | x :: y :: rest => (x, y) :: cycleToPairs (y :: rest)

-- Helper to find the weight of a specific edge
def findWeight (src dst : Var) (edges : List Edge) : Int :=
  match edges.find? (fun e => e.src == src && e.dst == dst) with
  | some e => e.weight
  | none => 0

-- Reconstructs the detailed path string
def formatDetailedCycle (c : List Var) (edges : List Edge) : String :=
  let pairs := cycleToPairs c

  -- 1. Build the path string (e.g., x ∈ y (+1) → y ∈ z (+1))
  let pathStrings := pairs.map (fun (src, dst) =>
    let w := findWeight src dst edges
    if w == 1 then s!"{src} ∈ {dst} (+1)"
    else if w == 0 then s!"{src} = {dst} (0)"
    else s!"{dst} ∈ {src} (-1)" -- Handles reverse edges if they appear in the cycle
  )
  let pathStr := String.intercalate " → " pathStrings

  -- 2. Build the algebraic summary
  -- This requires extracting the start, end, and accumulating the weights
  if pairs.length >= 2 then
    let startVar := c.head!
    let endVar := c.reverse.tail!.head!

    -- Sum weights of the forward path
    let forwardPairs := pairs.dropLast
    let forwardWeight := forwardPairs.foldl (fun acc (s, d) => acc + findWeight s d edges) 0

    -- Get the weight of the back edge
    let backEdgePair := pairs.getLast!
    let backWeight := findWeight backEdgePair.1 backEdgePair.2 edges

    let req1 := s!"l({endVar}) = l({startVar}) + {forwardWeight}"
    let req2 := if backWeight == 0 then s!"l({endVar}) = l({startVar})"
                else s!"l({endVar}) = l({startVar}) + {-backWeight}"

    s!"Contradiction Path: {pathStr}.\nRequires {req1} and {req2}."
  else
    pathStr

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "=== NF Stratification Validator (Bellman-Ford Edition) ==="
  stdout.putStrLn "Enter atomic formulas to build a conjunction."
  stdout.putStrLn "Accepted syntax: 'x = y' for equality, 'x e y' for membership."
  stdout.putStrLn "Type 'done' to evaluate the combined formula."

  let atoms ← readFormulas stdin stdout []
  match buildConjunction atoms with
  | none => stdout.putStrLn "Execution terminated. No formulas were entered."
  | some f =>
      stdout.putStrLn "\nEvaluating constraint graph with cycle detection..."
      match evaluateStratification f with
      | StratificationResult.success witness =>
          stdout.putStrLn "Result: The formula is stratifiable."
          stdout.putStrLn s!"Witness Context: {formatWitness witness}"
      | StratificationResult.failure cycle edges =>
          stdout.putStrLn "Result: Not stratifiable. A type contradiction was detected."
          stdout.putStrLn (formatDetailedCycle cycle edges)
