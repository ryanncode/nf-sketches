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
  | qpair : Var → Var → Var → Atomic -- p = <x, y>_Q
  | qproj1 : Var → Var → Atomic      -- z = π_1(p)
  | qproj2 : Var → Var → Atomic      -- z = π_2(p)
  | app : Var → Var → Var → Atomic   -- z = u(v)
  | lam : Var → Var → Var → Atomic   -- z = \lambda x. t
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
  | univ : Nat → String → Formula → Formula
  | comp : Nat → String → Formula → Formula
  deriving Repr, DecidableEq

def Formula.eq (x y : Var) : Formula := Formula.atom (Atomic.eq x y)
def Formula.mem (x y : Var) : Formula := Formula.atom (Atomic.mem x y)

--------------------------------------------------------------------------------
-- 2. CONSTRAINT GENERATION
--------------------------------------------------------------------------------
-- Converts atomic formulas into numerical constraints for the Bellman-Ford graph.
-- Note: This currently extracts constraints globally across the entire formula,
-- establishing the baseline of strict global stratification. Future iterations
-- aiming for weak stratification will need to partition this by binding scope.

abbrev ScopedVar := Var × Nat

structure Constraint where
  v1 : ScopedVar
  v2 : ScopedVar
  diff : Int
  directed : Bool := false -- If true, only generates a single directional edge
  deriving Repr, DecidableEq

def extractConstraintsAux (scope : Nat) : Formula → List Constraint
  | Formula.atom (Atomic.eq x y) => [{ v1 := (x, scope), v2 := (y, scope), diff := 0 }]
  | Formula.atom (Atomic.mem x y) => [{ v1 := (x, scope), v2 := (y, scope), diff := 1, directed := false }]
  | Formula.atom (Atomic.qpair p x y) =>
      -- p = <x, y>_Q. Quine pairs are homogeneous, so p, x, and y are all at the same type level.
      -- To avoid bidirectional cycles that would ruin DAG flattening, we establish directed 0-weight edges
      -- from the components to the pair.
      [{ v1 := (x, scope), v2 := (p, scope), diff := 0, directed := true },
       { v1 := (y, scope), v2 := (p, scope), diff := 0, directed := true }]
  | Formula.atom (Atomic.qproj1 z p) =>
      -- z = π_1(p). Directed 0-weight edge from p to z.
      [{ v1 := (p, scope), v2 := (z, scope), diff := 0, directed := true }]
  | Formula.atom (Atomic.qproj2 z p) =>
      -- z = π_2(p). Directed 0-weight edge from p to z.
      [{ v1 := (p, scope), v2 := (z, scope), diff := 0, directed := true }]
  | Formula.atom (Atomic.app z u v) =>
      -- z = u(v)
      -- For U(V) at type n, generate a 0-weight edge between vertex U(V) and vertex V.
      -- For the application rule (U at n+1, V at n), insert a directed edge from V to U with a weight of 1.
      [{ v1 := (v, scope), v2 := (z, scope), diff := 0 },
       { v1 := (v, scope), v2 := (u, scope), diff := 1, directed := true }]
  | Formula.atom (Atomic.lam z x t) =>
      -- z = \lambda x. t
      -- For \lambda x.T at type n, generate a 0-weight edge between vertex x and vertex T.
      -- For the abstraction rule (\lambda x.T at n, x at n-1), insert a directed edge from x to the composite vertex \lambda x.T with a weight of 1.
      [{ v1 := (x, scope), v2 := (t, scope), diff := 0 },
       { v1 := (x, scope), v2 := (z, scope), diff := 1, directed := true }]
  | Formula.neg p => extractConstraintsAux scope p
  | Formula.conj p q => extractConstraintsAux scope p ++ extractConstraintsAux scope q
  | Formula.disj p q => extractConstraintsAux scope p ++ extractConstraintsAux scope q
  | Formula.impl p q => extractConstraintsAux scope p ++ extractConstraintsAux scope q
  | Formula.univ n _ p => extractConstraintsAux n p
  | Formula.comp n _ p => extractConstraintsAux n p

def extractConstraints (f : Formula) : List Constraint :=
  extractConstraintsAux 0 f

--------------------------------------------------------------------------------
-- 3. GRAPH REPRESENTATION
--------------------------------------------------------------------------------
-- Defines the directed edges and weights for the constraint graph.

structure Edge where
  src : ScopedVar
  dst : ScopedVar
  weight : Int
  deriving Repr, DecidableEq

def buildEdges : List Constraint → List Edge
  | [] => []
  | c :: cs =>
      if c.directed then
        { src := c.v1, dst := c.v2, weight := c.diff } :: buildEdges cs
      else
        { src := c.v1, dst := c.v2, weight := c.diff } ::
        { src := c.v2, dst := c.v1, weight := -c.diff } ::
        buildEdges cs

def getVarsAux : List Constraint → List ScopedVar
  | [] => []
  | c :: cs => c.v1 :: c.v2 :: getVarsAux cs

def nub {α : Type} [DecidableEq α] (l : List α) : List α :=
  l.foldr (fun x acc => if acc.contains x then acc else x :: acc) []

def getVars (cs : List Constraint) : List ScopedVar :=
  nub (getVarsAux cs)

--------------------------------------------------------------------------------
-- 4. BELLMAN-FORD ALGORITHM (CYCLE DETECTION)
--------------------------------------------------------------------------------
-- The core engine for checking stratifiability. Evaluates sets of constraints
-- simultaneously by searching for negative weight cycles in a directed graph.

def lookup (l : List (ScopedVar × Int)) (k : ScopedVar) : Int :=
  match l with
  | [] => 0
  | (k', v) :: xs => if k == k' then v else lookup xs k

def update (l : List (ScopedVar × Int)) (k : ScopedVar) (v : Int) : List (ScopedVar × Int) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: xs => if k == k' then (k, v) :: xs else (k', v') :: update xs k v

def lookupPred (l : List (ScopedVar × ScopedVar)) (k : ScopedVar) : Option ScopedVar :=
  match l with
  | [] => none
  | (k', v) :: xs => if k == k' then some v else lookupPred xs k

def updatePred (l : List (ScopedVar × ScopedVar)) (k : ScopedVar) (v : ScopedVar) : List (ScopedVar × ScopedVar) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: xs => if k == k' then (k, v) :: xs else (k', v') :: updatePred xs k v

def relaxEdges (edges : List Edge) (dist : List (ScopedVar × Int)) (pred : List (ScopedVar × ScopedVar)) :
    List (ScopedVar × Int) × List (ScopedVar × ScopedVar) × Bool :=
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

def getCycleForward (pred : List (ScopedVar × ScopedVar)) (start : ScopedVar) (n : Nat) : List ScopedVar :=
  -- Trace backwards through the predecessor map `n` times to guarantee we land inside the cycle
  let rec goUp (curr : ScopedVar) (steps : Nat) : ScopedVar :=
    match steps with
    | 0 => curr
    | s + 1 => match lookupPred pred curr with
               | some p => goUp p s
               | none => curr
  let cycleStart := goUp start n

  -- From the guaranteed cycle node, trace backwards again until we hit a node we've already seen
  let rec collect (curr : ScopedVar) (acc : List ScopedVar) (fuel : Nat) : List ScopedVar :=
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
  | success (witness : List (Nat × List (Var × Int)))
  | failure (cycle : List ScopedVar) (edges : List Edge)

def getFormulaVarsAux (scope : Nat) : Formula → List ScopedVar
  | Formula.atom (Atomic.eq x y) => [(x, scope), (y, scope)]
  | Formula.atom (Atomic.mem x y) => [(x, scope), (y, scope)]
  | Formula.atom (Atomic.qpair p x y) => [(p, scope), (x, scope), (y, scope)]
  | Formula.atom (Atomic.qproj1 z p) => [(z, scope), (p, scope)]
  | Formula.atom (Atomic.qproj2 z p) => [(z, scope), (p, scope)]
  | Formula.atom (Atomic.app z u v) => [(z, scope), (u, scope), (v, scope)]
  | Formula.atom (Atomic.lam z x t) => [(z, scope), (x, scope), (t, scope)]
  | Formula.neg p => getFormulaVarsAux scope p
  | Formula.conj p q => getFormulaVarsAux scope p ++ getFormulaVarsAux scope q
  | Formula.disj p q => getFormulaVarsAux scope p ++ getFormulaVarsAux scope q
  | Formula.impl p q => getFormulaVarsAux scope p ++ getFormulaVarsAux scope q
  | Formula.univ n _ p => getFormulaVarsAux n p
  | Formula.comp n _ p => getFormulaVarsAux n p

def getFormulaVars (f : Formula) : List ScopedVar :=
  nub (getFormulaVarsAux 0 f)

def lookupNat (l : List (ScopedVar × Nat)) (k : ScopedVar) : Nat :=
  match l with
  | [] => 0
  | (k', v) :: xs => if k == k' then v else lookupNat xs k

def updateNat (l : List (ScopedVar × Nat)) (k : ScopedVar) (v : Nat) : List (ScopedVar × Nat) :=
  match l with
  | [] => [(k, v)]
  | (k', v') :: xs => if k == k' then (k, v) :: xs else (k', v') :: updateNat xs k v

def computeInDegrees (vars : List ScopedVar) (edges : List Edge) : List (ScopedVar × Nat) :=
  let init := vars.map (fun v => (v, 0))
  edges.foldl (fun acc e =>
    let currentIn := lookupNat acc e.dst
    updateNat acc e.dst (currentIn + 1)
  ) init

def topologicalSort (vars : List ScopedVar) (edges : List Edge) : Option (List ScopedVar) :=
  let inDegrees := computeInDegrees vars edges
  let initQueue := inDegrees.filter (fun p => p.2 == 0) |>.map (·.1)

  let rec loop (fuel : Nat) (queue : List ScopedVar) (inDegs : List (ScopedVar × Nat)) (sorted : List ScopedVar) : List ScopedVar :=
    match fuel with
    | 0 => sorted.reverse
    | f + 1 =>
        match queue with
        | [] => sorted.reverse
        | u :: qs =>
            let outgoing := edges.filter (fun e => e.src == u)
            let (newQueue, newInDegs) := outgoing.foldl (fun (q, degs) e =>
              let v := e.dst
              let deg := lookupNat degs v
              let nextDeg := deg - 1
              let degs' := updateNat degs v nextDeg
              if nextDeg == 0 then
                (v :: q, degs')
              else
                (q, degs')
            ) (qs, inDegs)
            loop f newQueue newInDegs (u :: sorted)

  let sorted := loop vars.length initQueue inDegrees []
  if sorted.length == vars.length then
    some sorted
  else
    none

def dagShortestPath (vars : List ScopedVar) (edges : List Edge) (sorted : List ScopedVar) : List (ScopedVar × Int) :=
  let initialDist : List (ScopedVar × Int) := vars.map (fun v => (v, (0 : Int)))
  sorted.foldl (fun dist u =>
    let outgoing := edges.filter (fun e => e.src == u)
    outgoing.foldl (fun d e =>
      let du := lookup d u
      let dv := lookup d e.dst
      if du + e.weight < dv then
        update d e.dst (du + e.weight)
      else
        d
    ) dist
  ) initialDist

def evaluateClause (vars : List ScopedVar) (constraints : List Constraint) : Except (List ScopedVar × List Edge) (List (ScopedVar × Int)) :=
  let edges := buildEdges constraints
  let n := vars.length

  if n == 0 then
    Except.ok []
  else
    -- Try O(V+E) DAG Topological Sort First
    match (none : Option (List ScopedVar)) with
    | some sorted =>
        let finalDist := dagShortestPath vars edges sorted
        Except.ok finalDist
    | none =>
        -- Fallback to Bellman-Ford for non-DAGs (containing cycles)
        let initialDist : List (ScopedVar × Int) := vars.map (fun v => (v, (0 : Int)))
        let initialPred : List (ScopedVar × ScopedVar) := []

        let rec loop (i : Nat) (d : List (ScopedVar × Int)) (p : List (ScopedVar × ScopedVar)) :=
          match i with
          | 0 => (d, p)
          | j + 1 =>
            let (d', p', changed) := relaxEdges edges d p
            if not changed then (d', p') else loop j d' p'

        let (finalDist, finalPred) := loop (n - 1) initialDist initialPred

        let (_, cyclePred, hasCycle) := relaxEdges edges finalDist finalPred
        if not hasCycle then
          Except.ok finalDist
        else
          let conflictNode := edges.findSome? (fun e =>
            let du := lookup finalDist e.src
            let dv := lookup finalDist e.dst
            if du + e.weight < dv then some e.dst else none
          )
          match conflictNode with
          | some node => Except.error (getCycleForward cyclePred node n, edges)
          | none => Except.error ([], edges)

def evaluateClausePartitioned (vars : List ScopedVar) (constraints : List Constraint) : StratificationResult :=
  let scopes := nub (vars.map (fun v => v.2))
  let rec evalScopes (ss : List Nat) (accWitness : List (Nat × List (Var × Int))) :=
    match ss with
    | [] => StratificationResult.success accWitness
    | s :: rest =>
      let sVars := vars.filter (fun v => v.2 == s)
      let sConstraints := constraints.filter (fun c => c.v1.2 == s)
      match evaluateClause sVars sConstraints with
      | Except.ok dist =>
          let scopeDist := dist.map (fun ⟨⟨v, _⟩, weight⟩ => (v, weight))
          evalScopes rest ((s, scopeDist) :: accWitness)
      | Except.error (cycle, edges) => StratificationResult.failure cycle edges
  evalScopes scopes []

def evaluateStratification (f : Formula) : StratificationResult :=
  let constraints := extractConstraints f
  evaluateClausePartitioned (getFormulaVars f) constraints

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
  | Formula.univ _ _ p => 1 + formulaSize p
  | Formula.comp _ _ p => 1 + formulaSize p

@[simp] theorem size_atom (a) : formulaSize (Formula.atom a) = 1 := rfl
@[simp] theorem size_neg (p) : formulaSize (Formula.neg p) = 1 + formulaSize p := rfl
@[simp] theorem size_conj (p q) : formulaSize (Formula.conj p q) = 1 + formulaSize p + formulaSize q := rfl
@[simp] theorem size_disj (p q) : formulaSize (Formula.disj p q) = 1 + formulaSize p + formulaSize q := rfl
@[simp] theorem size_impl (p q) : formulaSize (Formula.impl p q) = 1 + formulaSize p + formulaSize q := rfl
@[simp] theorem size_univ (n x p) : formulaSize (Formula.univ n x p) = 1 + formulaSize p := rfl
@[simp] theorem size_comp (n x p) : formulaSize (Formula.comp n x p) = 1 + formulaSize p := rfl

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
  | Formula.univ n x p =>
      have : formulaSize p < formulaSize (Formula.univ n x p) := by simp <;> try omega
      Formula.univ n x (pushNeg p)
  | Formula.comp n x p =>
      have : formulaSize p < formulaSize (Formula.comp n x p) := by simp <;> try omega
      Formula.comp n x (pushNeg p)
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
  | Formula.univ n x p => Formula.univ n x (toDNFForm p)
  | Formula.comp n x p => Formula.comp n x (toDNFForm p)
  | p => p

def extractLiteralsAux (scope : Nat) : Formula → List Constraint
  | Formula.atom (Atomic.eq x y) => [{ v1 := (x, scope), v2 := (y, scope), diff := 0 }]
  | Formula.atom (Atomic.mem x y) => [{ v1 := (x, scope), v2 := (y, scope), diff := 1, directed := false }]
  | Formula.atom (Atomic.qpair p x y) =>
      [{ v1 := (x, scope), v2 := (p, scope), diff := 0, directed := true },
       { v1 := (y, scope), v2 := (p, scope), diff := 0, directed := true }]
  | Formula.atom (Atomic.qproj1 z p) =>
      [{ v1 := (p, scope), v2 := (z, scope), diff := 0, directed := true }]
  | Formula.atom (Atomic.qproj2 z p) =>
      [{ v1 := (p, scope), v2 := (z, scope), diff := 0, directed := true }]
  -- Note: We drop negated literals because the Bellman-Ford algorithm only natively
  -- handles strict equalities and memberships. Inequalities are loosely enforced.
  | Formula.neg (Formula.atom (Atomic.eq _ _)) => []
  | Formula.neg (Formula.atom (Atomic.mem _ _)) => []
  | Formula.neg (Formula.atom (Atomic.qpair _ _ _)) => []
  | Formula.neg (Formula.atom (Atomic.qproj1 _ _)) => []
  | Formula.neg (Formula.atom (Atomic.qproj2 _ _)) => []
  | Formula.conj p q => extractLiteralsAux scope p ++ extractLiteralsAux scope q
  | Formula.univ n _ p => extractLiteralsAux n p
  | Formula.comp n _ p => extractLiteralsAux n p
  | _ => []

def extractLiterals (f : Formula) : List Constraint :=
  extractLiteralsAux 0 f

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
        match evaluateClausePartitioned vars c with
        | StratificationResult.success w => StratificationResult.success w
        | StratificationResult.failure cycle edges => checkClauses rest (some (StratificationResult.failure cycle edges))
  checkClauses clauses none

abbrev StratificationWitness := List (Nat × List (Var × Int))

def lookupScope (w : StratificationWitness) (scope : Nat) : List (Var × Int) :=
  match w with
  | [] => []
  | (s, l) :: xs => if scope == s then l else lookupScope xs scope

def lookupVarWeight (l : List (Var × Int)) (v : Var) : Int :=
  match l with
  | [] => 0
  | (v', weight) :: xs => if v == v' then weight else lookupVarWeight xs v

/--
Verifies if a StratificationWitness satisfies NFI (Impredicative Subsystem) bounds.
NFI permits mild impredicativity, meaning the maximum integer weight of any internal
variable vertex never exceeds the topological weight of the base element vertex
(plus 1 for the set itself, meaning variables are <= type(base_element) + 1).
For simplicity in this validator, we track if any variable exceeds the base element's type + 1.
Assuming the base element is Var.bound 0 at scope 0.
-/
def satisfiesNFI (w : StratificationWitness) : Bool :=
  w.all (fun ⟨s, l⟩ =>
    let baseWeight := lookupVarWeight l (Var.bound 0)
    l.all (fun ⟨_, weight⟩ => weight <= baseWeight + 1)
  )

/--
Verifies if a StratificationWitness satisfies NFP (Predicative Subsystem) bounds.
NFP strictly restricts graph validators to predicative bounds, enforcing that no
internal bound variable vertex exceeds the integer weight of the base element vertex.
Assuming the base element is Var.bound 0 at scope 0.
-/
def satisfiesNFP (w : StratificationWitness) : Bool :=
  w.all (fun ⟨s, l⟩ =>
    let baseWeight := lookupVarWeight l (Var.bound 0)
    l.all (fun ⟨v, weight⟩ =>
      match v with
      | Var.bound _ => weight <= baseWeight
      | _ => weight <= baseWeight + 1
    )
  )

def checkStrat (f : Formula) : Option StratificationWitness :=
  match evaluateFullFormula f with
  | StratificationResult.success w =>
      -- Natively enforce weak stratification limits (NFI)
      if satisfiesNFI w then some w else none
  | StratificationResult.failure _ _ => none

def formatDetailedCycle (cycle : List ScopedVar) (edges : List Edge) : String :=
  let rec formatEdges (cvars : List ScopedVar) : String :=
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

/--
The structural definition of the set of Natural Numbers (Frege-Russell cardinality).
N = {n | ∀s. (0 ∈ s ∧ (∀x. x ∈ s → x + 1 ∈ s)) → n ∈ s}
We simplify it to a formula testing NFI/NFP bounds:
A set `n` is in `N` if it belongs to all inductive sets `s`.
phi_N: ∀s (Inductive(s) → n ∈ s)
Inductive(s): 0 ∈ s ∧ (∀x. x ∈ s → x+1 ∈ s)
For our diagnostic, the type collision happens because `s` is quantified over
and `n` (the element we are defining `N` for) belongs to `s`.
In `n ∈ s`, `s` must be at type `type(n) + 1`.
But `s` is an inductive set of numbers, so it's a set of sets (like `N` itself).
We can approximate this with:
phi_N = ∀s (n ∈ s)
where `n` is `Var.bound 0` (the base element), and `s` is `Var.bound 1`.
Wait, we need the formula for the benchmark.
Let's use a standard approximation of the impredicative collision:
phi_N = Formula.univ 0 "s" (Formula.impl (Formula.mem (Var.free "0") (Var.bound 0)) (Formula.mem (Var.bound 1) (Var.bound 0)))
Wait, inside univ "s", `s` is `Var.bound 0`, and the base element `n` is `Var.bound 1`.
So:
Inductive(s) = Formula.mem (Var.free "zero") (Var.bound 0)
phi_N = Formula.univ 0 "s" (Formula.impl (Formula.mem (Var.free "zero") (Var.bound 0)) (Formula.mem (Var.bound 1) (Var.bound 0)))
Let's see the type assignments:
`Var.bound 0` (s) has type `t`.
`Var.free "zero"` has type `t - 1`.
`Var.bound 1` (n, the base element) has type `t - 1`.
So `s` has type `t`, `n` has type `t - 1`.
This means `s` is one level higher than `n`.
The base element is `Var.bound 1` (n), with weight `t - 1`.
The internal variable `s` (Var.bound 0) has weight `t`.
Since `t = (t - 1) + 1`, `s` has weight exactly `baseWeight + 1`.
In NFI, `s` (weight `t`) <= `baseWeight + 1`, which is `t - 1 + 1 = t`. This passes!
In NFP, `s` is a bound variable. NFP requires `bound_weight <= baseWeight`. So `t <= t - 1`, which fails!
Let's run this diagnostic!
-/
def phi_N : Formula :=
  Formula.univ 1 "s" (
    Formula.mem (Var.bound 1) (Var.bound 0)
  )

def nfMain : IO Unit := do
  IO.println "Running Phase 3.1 & 3.3 Diagnostics (NFI vs NFP)"
  match checkStrat phi_N with
  | some w =>
      IO.println "Stratification Successful (General Weak Stratification)."
      IO.println s!"Witness: {reprStr w}"
      let baseWeight := lookupVarWeight (lookupScope w 1) (Var.bound 1) -- 'n' is bound 1 at scope 1
      IO.println s!"Base Element (n) Weight: {baseWeight}"

      let nfiPass := w.all (fun ⟨s, l⟩ =>
        let base_w := lookupVarWeight l (Var.bound 1)
        l.all (fun ⟨_, weight⟩ => weight <= base_w + 1)
      )
      let nfpPass := w.all (fun ⟨s, l⟩ =>
        let base_w := lookupVarWeight l (Var.bound 1)
        l.all (fun ⟨v, weight⟩ =>
          match v with
          | Var.bound _ => weight <= base_w
          | _ => weight <= base_w + 1
        )
      )

      IO.println s!"NFI (Impredicative) Check: {if nfiPass then "PASS" else "FAIL"}"
      IO.println s!"NFP (Predicative) Check: {if nfpPass then "PASS" else "FAIL"}"

      if nfiPass && not nfpPass then
        IO.println "Diagnostic SUCCESS: Natural numbers successfully route in NFI but are rejected in NFP!"
      else
        IO.println "Diagnostic FAILED to distinguish NFI and NFP correctly."
  | none =>
      IO.println "Stratification Failed entirely."
