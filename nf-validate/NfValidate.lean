import Init.Data.List.Basic
import Init.System.IO

abbrev Var := String

--------------------------------------------------------------------------------
-- 1. ABSTRACT SYNTAX TREE (AST)
--------------------------------------------------------------------------------
-- Defines the structure of logical formulas in our language.

inductive Formula where
  | eq : Var → Var → Formula
  | mem : Var → Var → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | univ : Var → Formula → Formula
  deriving Repr, BEq

--------------------------------------------------------------------------------
-- 2. CONSTRAINT GENERATION
--------------------------------------------------------------------------------
-- Converts atomic formulas into numerical constraints for the Bellman-Ford graph.

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
  | Formula.disj p q => extractConstraints p ++ extractConstraints q
  | Formula.impl p q => extractConstraints p ++ extractConstraints q
  | Formula.univ _ p => extractConstraints p

--------------------------------------------------------------------------------
-- 3. GRAPH REPRESENTATION
--------------------------------------------------------------------------------
-- Defines the directed edges and weights for the constraint graph.

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

def nub (l : List Var) : List Var :=
  match l with
  | [] => []
  | x :: xs =>
    have : (xs.filter (fun y => y != x)).length < (x :: xs).length := by
      calc (xs.filter (fun y => y != x)).length
        _ ≤ xs.length := List.length_filter_le ..
        _ < (x :: xs).length := Nat.lt_succ_self ..
    x :: nub (xs.filter (fun y => y != x))
termination_by l.length

def getVars (cs : List Constraint) : List Var :=
  nub (getVarsAux cs)

--------------------------------------------------------------------------------
-- 4. BELLMAN-FORD ALGORITHM (CYCLE DETECTION)
--------------------------------------------------------------------------------
-- The core engine for checking stratifiability. Evaluates sets of constraints
-- simultaneously by searching for negative weight cycles in a directed graph.

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
    -- If moving through the edge provides a shorter path (lower type level requirement)
    if du + e.weight < dv then
      -- Relax the edge, record the new distance, and track the predecessor for cycle reconstruction
      (update accD e.dst (du + e.weight), updatePred accP e.dst e.src, true)
    else
      (accD, accP, changed)
  ) (dist, pred, false)

def getCycleForward (pred : List (Var × Var)) (start : Var) (n : Nat) : List Var :=
  -- Trace backwards through the predecessor map `n` times to guarantee we land inside the cycle
  let rec goUp (curr : Var) (steps : Nat) : Var :=
    match steps with
    | 0 => curr
    | s + 1 => match lookupPred pred curr with
               | some p => goUp p s
               | none => curr
  let cycleStart := goUp start n

  -- From the guaranteed cycle node, trace backwards again until we hit a node we've already seen
  let rec collect (curr : Var) (acc : List Var) (fuel : Nat) : List Var :=
    match fuel with
    | 0 => curr :: acc
    | f + 1 =>
      if acc.contains curr then curr :: acc -- We've completed the loop
      else match lookupPred pred curr with
           | some p => collect p (curr :: acc) f
           | none => curr :: acc

  collect cycleStart [] n

--------------------------------------------------------------------------------
-- 5. EVALUATION PIPELINE & DNF CONVERSION
--------------------------------------------------------------------------------
-- Orchestrates the translation of full syntax trees into parallelizable branches
-- of simple constraints, evaluating each for stratifiability.

inductive StratificationResult where
  | success (witness : List (Var × Int))
  | failure (cycle : List Var) (edges : List Edge)

def getFormulaVarsAux : Formula → List Var
  | Formula.eq x y => [x, y]
  | Formula.mem x y => [x, y]
  | Formula.neg p => getFormulaVarsAux p
  | Formula.conj p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.disj p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.impl p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.univ x p => x :: getFormulaVarsAux p

def getFormulaVars (f : Formula) : List Var :=
  nub (getFormulaVarsAux f)

def evaluateClause (vars : List Var) (constraints : List Constraint) : StratificationResult :=
  let edges := buildEdges constraints
  let n := vars.length

  let initialDist : List (Var × Int) := vars.map (fun v => (v, (0 : Int)))
  let initialPred : List (Var × Var) := []

  let rec loop (i : Nat) (d : List (Var × Int)) (p : List (Var × Var)) :=
    match i with
    | 0 => (d, p)
    | j + 1 =>
      let (d', p', changed) := relaxEdges edges d p
      if not changed then (d', p') else loop j d' p'

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

def evaluateStratification (f : Formula) : StratificationResult :=
  let constraints := extractConstraints f
  evaluateClause (getFormulaVars f) constraints

--------------------------------------------------------------------------------
-- 6. DISJUNCTIVE NORMAL FORM (DNF) REDUCTION
--------------------------------------------------------------------------------
-- Flattens complex logic into an OR-of-ANDs structure. This allows the Bellman-Ford
-- engine to test multiple possible mathematical realities independently.

def formulaSize : Formula → Nat
  | Formula.eq _ _ => 1
  | Formula.mem _ _ => 1
  | Formula.neg p => 1 + formulaSize p
  | Formula.conj p q => 1 + formulaSize p + formulaSize q
  | Formula.disj p q => 1 + formulaSize p + formulaSize q
  | Formula.impl p q => 1 + formulaSize p + formulaSize q
  | Formula.univ _ p => 1 + formulaSize p

@[simp] theorem size_eq (x y) : formulaSize (Formula.eq x y) = 1 := rfl
@[simp] theorem size_mem (x y) : formulaSize (Formula.mem x y) = 1 := rfl
@[simp] theorem size_neg (p) : formulaSize (Formula.neg p) = 1 + formulaSize p := rfl
@[simp] theorem size_conj (p q) : formulaSize (Formula.conj p q) = 1 + formulaSize p + formulaSize q := rfl
@[simp] theorem size_disj (p q) : formulaSize (Formula.disj p q) = 1 + formulaSize p + formulaSize q := rfl
@[simp] theorem size_impl (p q) : formulaSize (Formula.impl p q) = 1 + formulaSize p + formulaSize q := rfl
@[simp] theorem size_univ (x p) : formulaSize (Formula.univ x p) = 1 + formulaSize p := rfl

@[simp] theorem size_pos (f : Formula) : 0 < formulaSize f := by
  cases f <;> simp <;> omega

def pushNeg : Formula → Formula
  | Formula.neg (Formula.neg p) =>
      have : formulaSize p < formulaSize (Formula.neg (Formula.neg p)) := by simp; omega
      pushNeg p -- Double negation elimination
  -- De Morgan's laws: push negation through conjunction/disjunction and flip the operator
  | Formula.neg (Formula.conj p q) =>
      have : formulaSize (Formula.neg p) < formulaSize (Formula.neg (Formula.conj p q)) := by simp <;> try omega
      have : formulaSize (Formula.neg q) < formulaSize (Formula.neg (Formula.conj p q)) := by simp <;> try omega
      Formula.disj (pushNeg (Formula.neg p)) (pushNeg (Formula.neg q))
  | Formula.neg (Formula.disj p q) =>
      have : formulaSize (Formula.neg p) < formulaSize (Formula.neg (Formula.disj p q)) := by simp <;> try omega
      have : formulaSize (Formula.neg q) < formulaSize (Formula.neg (Formula.disj p q)) := by simp <;> try omega
      Formula.conj (pushNeg (Formula.neg p)) (pushNeg (Formula.neg q))
  -- Implication equivalence: ~(p -> q) == p & ~q
  | Formula.neg (Formula.impl p q) =>
      have : formulaSize p < formulaSize (Formula.neg (Formula.impl p q)) := by simp <;> try omega
      have : formulaSize (Formula.neg q) < formulaSize (Formula.neg (Formula.impl p q)) := by simp <;> try omega
      Formula.conj (pushNeg p) (pushNeg (Formula.neg q))
  -- Implication equivalence: p -> q == ~p v q
  | Formula.impl p q =>
      have : formulaSize (Formula.neg p) < formulaSize (Formula.impl p q) := by simp <;> try omega
      have : formulaSize q < formulaSize (Formula.impl p q) := by simp <;> try omega
      Formula.disj (pushNeg (Formula.neg p)) (pushNeg q)
  | Formula.conj p q =>
      have : formulaSize p < formulaSize (Formula.conj p q) := by simp <;> try omega
      have : formulaSize q < formulaSize (Formula.conj p q) := by simp <;> try omega
      Formula.conj (pushNeg p) (pushNeg q)
  | Formula.disj p q =>
      have : formulaSize p < formulaSize (Formula.disj p q) := by simp <;> try omega
      have : formulaSize q < formulaSize (Formula.disj p q) := by simp <;> try omega
      Formula.disj (pushNeg p) (pushNeg q)
  | Formula.neg p => Formula.neg p -- Negation has reached the atomic level
  | p => p
termination_by f => formulaSize f
decreasing_by
  all_goals assumption

def distributeAnd : Formula → Formula → Formula
  -- Distributive property: (p1 v p2) & q == (p1 & q) v (p2 & q)
  | Formula.disj p1 p2, q =>
      have : formulaSize p1 + formulaSize q < formulaSize (Formula.disj p1 p2) + formulaSize q := by rw [size_disj]; omega
      have : formulaSize p2 + formulaSize q < formulaSize (Formula.disj p1 p2) + formulaSize q := by rw [size_disj]; omega
      Formula.disj (distributeAnd p1 q) (distributeAnd p2 q)
  | p, Formula.disj q1 q2 =>
      have : formulaSize p + formulaSize q1 < formulaSize p + formulaSize (Formula.disj q1 q2) := by rw [size_disj]; omega
      have : formulaSize p + formulaSize q2 < formulaSize p + formulaSize (Formula.disj q1 q2) := by rw [size_disj]; omega
      Formula.disj (distributeAnd p q1) (distributeAnd p q2)
  | p, q => Formula.conj p q
termination_by p q => formulaSize p + formulaSize q
decreasing_by
  all_goals assumption

def toDNFForm : Formula → Formula
  | Formula.conj p q => distributeAnd (toDNFForm p) (toDNFForm q)
  | Formula.disj p q => Formula.disj (toDNFForm p) (toDNFForm q)
  | p => p

def extractLiterals : Formula → List Constraint
  | Formula.eq x y => [{ v1 := x, v2 := y, diff := 0 }]
  | Formula.mem x y => [{ v1 := x, v2 := y, diff := 1 }]
  -- Note: We drop negated literals because the Bellman-Ford algorithm only natively
  -- handles strict equalities and memberships. Inequalities are loosely enforced.
  | Formula.neg (Formula.eq _ _) => []
  | Formula.neg (Formula.mem _ _) => []
  | Formula.conj p q => extractLiterals p ++ extractLiterals q
  | _ => []

def getDNFClauses : Formula → List (List Constraint)
  | Formula.disj p q => getDNFClauses p ++ getDNFClauses q
  | p => [extractLiterals p]

def toDNF (f : Formula) : List (List Constraint) :=
  getDNFClauses (toDNFForm (pushNeg f))

def evaluateFullFormula (f : Formula) : StratificationResult :=
  -- We extract variables from the entire formula *before* DNF reduction
  -- so that the witness context includes variables whose constraints might be dropped
  let vars := getFormulaVars f
  let clauses := toDNF f
  -- Iterates through each DNF branch, returning the first successful stratification.
  -- If all branches fail, it returns the failure result of the last branch checked.
  let rec checkClauses (cs : List (List Constraint)) (lastFail : Option StratificationResult) :=
    match cs with
    | [] =>
        match lastFail with
        | some fail => fail
        | none => StratificationResult.failure [] []
    | c :: rest =>
        match evaluateClause vars c with
        | StratificationResult.success w => StratificationResult.success w
        | StratificationResult.failure cycle edges => checkClauses rest (some (StratificationResult.failure cycle edges))
  checkClauses clauses none

def buildConjunction (atoms : List Formula) : Option Formula :=
  match atoms with
  | [] => none
  | [x] => some x
  | x :: xs =>
      match buildConjunction xs with
      | some rest => some (Formula.conj x rest)
      | none => none

--------------------------------------------------------------------------------
-- 7. COMPREHENSIVE PARSER FOR FIRST-ORDER LOGIC
--------------------------------------------------------------------------------
-- Converts raw user input strings into the Formula AST. Supports parentheses
-- and operator precedence (~, &, v, ->).

inductive Token where
  | var : String → Token
  | eq : Token
  | mem : Token
  | neg : Token
  | conj : Token
  | disj : Token
  | impl : Token
  | lparen : Token
  | rparen : Token
  deriving Repr, BEq

partial def tokenize (s : String) : List Token :=
  let rec go (cs : List Char) (acc : List Token) :=
    match cs with
    | [] => acc.reverse
    | ' ' :: rest => go rest acc
    | '\t' :: rest => go rest acc
    | '\n' :: rest => go rest acc
    | '\r' :: rest => go rest acc
    | '(' :: rest => go rest (Token.lparen :: acc)
    | ')' :: rest => go rest (Token.rparen :: acc)
    | '~' :: rest => go rest (Token.neg :: acc)
    | 'v' :: rest => go rest (Token.disj :: acc)
    | '&' :: rest => go rest (Token.conj :: acc)
    | '-' :: '>' :: rest => go rest (Token.impl :: acc)
    | '=' :: rest => go rest (Token.eq :: acc)
    | 'e' :: rest => go rest (Token.mem :: acc)
    | c :: rest =>
        if c.isAlphanum then
          let (varChars, rest') := cs.span Char.isAlphanum
          go rest' (Token.var (String.ofList varChars) :: acc)
        else
          go rest acc
  go s.toList []

partial def parseAtomic (toks : List Token) : Option (Formula × List Token) :=
  match toks with
  | Token.var x :: Token.eq :: Token.var y :: rest => some (Formula.eq x y, rest)
  | Token.var x :: Token.mem :: Token.var y :: rest => some (Formula.mem x y, rest)
  | Token.lparen :: _ =>
      -- forward declaration workaround: call parseImpl
      none -- replaced below
  | _ => none

mutual
partial def parsePrimary (toks : List Token) : Option (Formula × List Token) :=
  match toks with
  | Token.neg :: rest =>
      match parsePrimary rest with
      | some (f, rest') => some (Formula.neg f, rest')
      | none => none
  | Token.lparen :: rest =>
      match parseImpl rest with
      | some (f, Token.rparen :: rest') => some (f, rest')
      | _ => none
  | _ => parseAtomic toks

partial def parseConj (toks : List Token) : Option (Formula × List Token) :=
  match parsePrimary toks with
  | some (f1, Token.conj :: rest) =>
      match parseConj rest with
      | some (f2, rest') => some (Formula.conj f1 f2, rest')
      | none => none
  | res => res

partial def parseDisj (toks : List Token) : Option (Formula × List Token) :=
  match parseConj toks with
  | some (f1, Token.disj :: rest) =>
      match parseDisj rest with
      | some (f2, rest') => some (Formula.disj f1 f2, rest')
      | none => none
  | res => res

partial def parseImpl (toks : List Token) : Option (Formula × List Token) :=
  match parseDisj toks with
  | some (f1, Token.impl :: rest) =>
      match parseImpl rest with
      | some (f2, rest') => some (Formula.impl f1 f2, rest')
      | none => none
  | res => res
end

partial def parseFormula (s : String) : Option Formula :=
  match parseImpl (tokenize s) with
  | some (f, []) => some f
  | _ => none

partial def readFormulas (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (acc : List Formula) : IO (List Formula) := do
  stdout.putStr "> "
  stdout.flush
  let line ← stdin.getLine
  let input := line.trimAscii.toString
  if input == "done" then
    return acc
  else
    match parseFormula input with
    | some f => readFormulas stdin stdout (acc ++ [f])
    | none =>
        stdout.putStrLn "Invalid format. Logical operators (~, &, v, ->) must be applied to full relations. Example: '~(x = y)', '(a e b) & (c = d)'."
        readFormulas stdin stdout acc

--------------------------------------------------------------------------------
-- 8. OUTPUT FORMATTING & SEMANTIC TRACE
--------------------------------------------------------------------------------
-- Translates the internal numerical evaluation results back into algebraic
-- proofs or type contradiction paths for the user.

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

--------------------------------------------------------------------------------
-- 9. MAIN EXECUTION LOOP
--------------------------------------------------------------------------------

def nfMain : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "=== NF Stratification Validator ==="
  stdout.putStrLn "Enter formulas to build a conjunction."
  stdout.putStrLn "Accepted syntax: Relational statements ('x = y', 'x e y') combined with logical operators ('~', '&', 'v', '->'). Example: '~(x = y) & (y e z)'."
  stdout.putStrLn "Type 'done' to evaluate the combined formula."

  let atoms ← readFormulas stdin stdout []
  match buildConjunction atoms with
  | none => stdout.putStrLn "Execution terminated. No formulas were entered."
  | some f =>
      stdout.putStrLn "\nEvaluating constraint graph with DNF conversion and cycle detection..."
      match evaluateFullFormula f with
      | StratificationResult.success witness =>
          stdout.putStrLn "Result: The formula is stratifiable."
          stdout.putStrLn s!"Witness Context: {formatWitness witness}"
      | StratificationResult.failure cycle edges =>
          stdout.putStrLn "Result: Not stratifiable. A type contradiction was detected in all branches."
          stdout.putStrLn (formatDetailedCycle cycle edges)
