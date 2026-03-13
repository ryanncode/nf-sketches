import NfValidate

/-!
# ParseStrat: Shared Library and Formatting Tools

This module serves as the root of the `ParseStrat` library, providing shared
formatting and diagnostic helper functions that translate the internal
numerical evaluation results of `nf-validate` back into readable algebraic
proofs and type contradiction paths.
-/

--------------------------------------------------------------------------------
-- 1. VARIABLE AND WITNESS FORMATTING
--------------------------------------------------------------------------------
-- Basic string conversion for variables and the successful stratification
-- witness context.

def varToString : Var → String
  | Var.free s => s
  | Var.bound n => s!"_{n}"

def formatWitness (w : List (Var × Int)) : String :=
  let pairs := w.map (fun (v, l) => s!"{varToString v} : {l}")
  "{" ++ String.intercalate ", " pairs ++ "}"

--------------------------------------------------------------------------------
-- 2. CYCLE PATH RECONSTRUCTION & FORMATTING
--------------------------------------------------------------------------------
-- Translates the raw nodes and edges returned by the Bellman-Ford failure
-- case into a human-readable algebraic contradiction path.

-- Helper to convert a list of variables into pairs of adjacent nodes
def cycleToPairs (c : List Var) : List (Var × Var) :=
  let rec go (lst : List Var) : List (Var × Var) :=
    match lst with
    | [] => []
    | [_] => []
    | x :: y :: rest => (x, y) :: go (y :: rest)
  match c with
  | [] => []
  | [x] => [(x, x)]
  | lst => go lst

-- Helper to find the weight of a specific edge
def findWeight (src dst : Var) (edges : List Edge) : Int :=
  let candidateEdges := edges.filter (fun e => e.src == src && e.dst == dst)
  let edge := candidateEdges.foldl (fun minOpt e =>
    match minOpt with
    | none => some e
    | some min_e => if e.weight < min_e.weight then some e else some min_e
  ) (none : Option Edge)
  match edge with
  | some e => e.weight
  | none => 0

deriving instance Inhabited for Var

/--
Reconstructs the detailed path string from a given cycle and list of edges.
It dynamically calculates the total algebraic contradiction weight and formats
the output to explicitly demonstrate the unstratifiable nature of the cycle.
-/
def formatDetailedCycleSandbox (c : List Var) (edges : List Edge) : String :=
  let pairs := cycleToPairs c

  -- 1. Build the path string (e.g., x ∈ y (+1) → y ∈ z (+1))
  let pathStrings := pairs.map (fun (src, dst) =>
    let w := findWeight src dst edges
    if w == 1 then s!"{varToString src} ∈ {varToString dst} (+1)"
    else if w == 0 then s!"{varToString src} = {varToString dst} (0)"
    else s!"{varToString dst} ∈ {varToString src} (-1)" -- Handles reverse edges if they appear in the cycle
  )
  let pathStr := String.intercalate " → " pathStrings

  -- 2. Build the algebraic summary
  if pairs.length > 0 then
    let startVar := c.head!
    let totalWeight := pairs.foldl (fun acc (s, d) => acc + findWeight s d edges) 0
    let req := s!"l({varToString startVar}) = l({varToString startVar}) + {totalWeight}"
    s!"Contradiction Path: {pathStr}\n  Requires {req}"
  else
    pathStr
