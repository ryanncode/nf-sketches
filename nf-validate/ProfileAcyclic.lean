import NfValidate
import NfValidate.BowlerTranslation

open Bowler

-- Profiling the Bowler acyclic translation

instance : Inhabited Formula where
  default := Formula.atom (Atomic.eq (Var.free "x") (Var.free "y"))

partial def balancedConj : List Formula → Formula
  | [] => Formula.mem (Var.free "a") (Var.free "b")
  | [x] => x
  | xs =>
      let mid := xs.length / 2
      let (left, right) := xs.splitAt mid
      Formula.conj (balancedConj left) (balancedConj right)

-- Generates a single cycle of n variables: v_0 = v_1, v_1 = v_2, ..., v_{n-1} = v_0
def makeCycle (c : Nat) (n : Nat) : Formula :=
  if n < 2 then Formula.mem (Var.free "a") (Var.free "b") else
  let vars := List.range n |>.map (fun i => Var.free s!"v_{c}_{i}")
  let eqs := List.range n |>.map (fun i =>
    let v1 := vars.getD i (Var.free "")
    let v2 := vars.getD ((i + 1) % n) (Var.free "")
    Formula.eq v1 v2
  )
  balancedConj eqs

-- Generates a "Broad Matrix" of K completely disjoint cycles, each of size N.
def makeBroadMatrix (k : Nat) (n : Nat) : Formula :=
  let blocks := List.range k |>.map (fun c => makeCycle c n)
  balancedConj blocks

-- A simple accumulator to forcefully evaluate the entire AST
-- without incurring the deep recursive call-stack penalty.
partial def hashAST : List Formula → UInt64 → UInt64
  | [], acc => acc
  | Formula.atom _ :: rest, acc => hashAST rest (acc + 1)
  | Formula.neg p :: rest, acc => hashAST (p :: rest) (acc + 2)
  | Formula.conj p q :: rest, acc => hashAST (p :: q :: rest) (acc + 3)
  | Formula.disj p q :: rest, acc => hashAST (p :: q :: rest) (acc + 4)
  | Formula.impl p q :: rest, acc => hashAST (p :: q :: rest) (acc + 5)
  | Formula.univ _ _ p :: rest, acc => hashAST (p :: rest) (acc + 6)
  | Formula.comp _ _ p :: rest, acc => hashAST (p :: rest) (acc + 7)

def forceAST (f : Formula) : UInt64 :=
  hashAST [f] 0

def timePure {α : Type} (msg : String) (f : Unit → α) : IO α := do
  let start ← IO.monoMsNow
  let res := f ()
  let finish ← IO.monoMsNow
  IO.println s!"{msg}{finish - start} ms"
  pure res

def profileFormula (k : Nat) (n : Nat) : IO Unit := do
  IO.println s!"Broad Matrix [K={k} cycles of N={n}] (V={k*n}, E={k*n}):"

  -- Use IO.rand to defeat the Lean compiler's let-floating optimizer,
  -- ensuring the pure computations happen INSIDE the timeit block.
  let f ← timeit "  AST Gen Time:     " (do
    let k' ← IO.rand 0 0
    pure (makeBroadMatrix (k + k') n)
  )

  -- Graph semantic extraction & SCC detection
  let (_, _, _, cyclicSccs) ← timeit "  Graph + SCC Time: " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure f else pure f
    let c := extractConstraints f'
    let e := buildEdges c
    let v := getFormulaVars f'
    let s := findSCCs v e
    pure (c, e, v, s.filter (fun scc => scc.length > 1))
  )

  -- AST Algebraic Rewriting
  let fFlat ← timeit "  AST Rewrite Time: " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure f else pure f
    pure (flattenGraph f')
  )

  -- Force total evaluation
  let h ← timeit "  AST Hash Check:   " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure fFlat else pure fFlat
    pure (forceAST f')
  )

  IO.println s!"  Cycles Detected:  {cyclicSccs.length}"
  IO.println s!"  AST Hash Result:  {h}\n"

def main : IO Unit := do
  IO.println "Profiling Acyclic Translation (flattenGraph) with Broad Matrix..."
  IO.println "\n--- Test 1: Scaling K (Many Small Cycles, Tests Memory & AST Traversal) ---"
  for k in [128, 256, 512, 1024] do
    profileFormula k 5

  IO.println "\n--- Test 2: Scaling N (Large Single Cycles, Tests findSCCs O(N^2) behavior) ---"
  for n in [512, 1024, 2048, 4096] do
    profileFormula 1 n
