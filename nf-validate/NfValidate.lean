import Init.Data.List.Basic

/-!
# NF Validate: Core Syntax and Evaluation Pipeline

This module implements the core AST and evaluation engine for validating the stratification
of formulas in Quine's New Foundations (NF).

A key architectural decision is the bifurcation of the Abstract Syntax Tree (AST) into
dedicated atomic and compound types. This frames our functional programming choices as a
direct response to the limitations of classical Natural Deduction, separating the
targeted set theory constraints (which require geometric validation) from standard
first-order logical mechanics.
-/

inductive Var where
  | free : String → Var
  | bound : Nat → Var
  deriving Repr, DecidableEq

--------------------------------------------------------------------------------
-- 1. ABSTRACT SYNTAX TREE (AST)
--------------------------------------------------------------------------------
-- Defines the structure of logical formulas in our language.

/--
The `Atomic` type isolates the foundational relations of set theory: equality and membership.
By separating these into a dedicated type, we establish a structural boundary that allows
the constraint generation engine to focus exclusively on the targeted set theory constraints
that dictate type levels, distinct from the broader boolean logic.
-/
inductive Atomic where
  | eq : Var → Var → Atomic
  | mem : Var → Var → Atomic
  deriving Repr, DecidableEq

/--
The `Formula` type represents the compound logical structure.
It wraps the `Atomic` relations and defines the standard first-order mechanics (negation,
conjunction, disjunction, implication, and universal quantification). This bifurcation
from the atomic constraints enables the evaluation pipeline to process logical branching
(like DNF conversion) independently of the geometric bounds checking, addressing the
limitations of classical Natural Deduction when dealing with stratification.
-/
inductive Formula where
  | atom : Atomic → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | univ : String → Formula → Formula
  deriving Repr, DecidableEq

def Formula.eq (x y : Var) : Formula := Formula.atom (Atomic.eq x y)
def Formula.mem (x y : Var) : Formula := Formula.atom (Atomic.mem x y)

--------------------------------------------------------------------------------
-- 2. CONSTRAINT GENERATION
--------------------------------------------------------------------------------
-- Converts atomic formulas into numerical constraints for the Bellman-Ford graph.

structure Constraint where
  v1 : Var
  v2 : Var
  diff : Int
  deriving Repr, DecidableEq

def extractConstraints : Formula → List Constraint
  | Formula.atom (Atomic.eq x y) => [{ v1 := x, v2 := y, diff := 0 }]
  | Formula.atom (Atomic.mem x y) => [{ v1 := x, v2 := y, diff := 1 }]
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
  deriving Repr, DecidableEq

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
  | Formula.atom (Atomic.eq x y) => [x, y]
  | Formula.atom (Atomic.mem x y) => [x, y]
  | Formula.neg p => getFormulaVarsAux p
  | Formula.conj p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.disj p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.impl p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.univ _ p => getFormulaVarsAux p

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

  let (_, cyclePred, hasCycle) := relaxEdges edges finalDist finalPred
  if not hasCycle then
    StratificationResult.success finalDist
  else
    let conflictNode := edges.findSome? (fun e =>
      let du := lookup finalDist e.src
      let dv := lookup finalDist e.dst
      if du + e.weight < dv then some e.dst else none
    )
    match conflictNode with
    | some node => StratificationResult.failure (getCycleForward cyclePred node n) edges
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
  | Formula.atom _ => 1
  | Formula.neg p => 1 + formulaSize p
  | Formula.conj p q => 1 + formulaSize p + formulaSize q
  | Formula.disj p q => 1 + formulaSize p + formulaSize q
  | Formula.impl p q => 1 + formulaSize p + formulaSize q
  | Formula.univ _ p => 1 + formulaSize p

@[simp] theorem size_atom (a) : formulaSize (Formula.atom a) = 1 := rfl
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
  | Formula.atom (Atomic.eq x y) => [{ v1 := x, v2 := y, diff := 0 }]
  | Formula.atom (Atomic.mem x y) => [{ v1 := x, v2 := y, diff := 1 }]
  -- Note: We drop negated literals because the Bellman-Ford algorithm only natively
  -- handles strict equalities and memberships. Inequalities are loosely enforced.
  | Formula.neg (Formula.atom (Atomic.eq _ _)) => []
  | Formula.neg (Formula.atom (Atomic.mem _ _)) => []
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

abbrev StratificationWitness := List (Var × Int)

def checkStrat (f : Formula) : Option StratificationWitness :=
  match evaluateFullFormula f with
  | StratificationResult.success w => some w
  | StratificationResult.failure _ _ => none

def formatDetailedCycle (cycle : List Var) (edges : List Edge) : String :=
  let rec formatEdges (cvars : List Var) : String :=
    match cvars with
    | [] => ""
    | [v] => s!"{reprStr v}"
    | u :: v :: rest =>
        -- Bellman-Ford traverses the shortest path, so we must extract the minimum weight edge
        let candidateEdges := edges.filter (fun e => e.src == u && e.dst == v)
        let edge := candidateEdges.foldl (fun minOpt e =>
          match minOpt with
          | none => some e
          | some min_e => if e.weight < min_e.weight then some e else some min_e
        ) (none : Option Edge)

        let weightStr := match edge with
                         | some e => s!" --({e.weight})--> "
                         | none => " --(?)--> "
        s!"{reprStr u}{weightStr}" ++ formatEdges (v :: rest)
  formatEdges cycle

def nfMain : IO Unit := pure ()
