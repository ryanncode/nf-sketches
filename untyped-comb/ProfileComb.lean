import UntypedComb
import UntypedComb.Core
import UntypedComb.DAG
import UntypedComb.Reduction
import UntypedComb.CombLib.Recursion
import UntypedComb.CombLib.SelfModels

open UntypedComb
open UntypedComb.CombLib.SelfModels
open Comb

-- A simple accumulator to forcefully evaluate the entire AST
-- without incurring deep recursive call-stack penalty for lazy verification
partial def hashComb : Comb → UInt64 → UInt64
  | Comb.S, acc => acc + 1
  | Comb.K, acc => acc + 2
  | Comb.I, acc => acc + 3
  | Comb.U, acc => acc + 4
  | Comb.var _, acc => acc + 5
  | Comb.t_inject c, acc => hashComb c (acc + 6)
  | Comb.lazy_thunk c, acc => hashComb c (acc + 7)
  | Comb.terminal _, acc => acc + 8
  | Comb.app c1 c2, acc => hashComb c2 (hashComb c1 (acc + 9))

def forceComb (c : Comb) : UInt64 :=
  hashComb c 0

-- Generates a massive nested chain to test DAG translation scaling
partial def makeDeepChain : Nat → Comb
  | 0 => Comb.I
  | n + 1 => Comb.app Comb.S (makeDeepChain n)

-- Evaluates the unstratified graph saturated with recursion
def makeSaturatedCycle (depth : Nat) : Comb :=
  -- Applying the Y combinator to a deeply nested payload
  Comb.app UntypedComb.Recursion.Y (makeDeepChain depth)

def profileComb (k : Nat) : IO Unit := do
  IO.println s!"Deep Chain [Depth={k}]:"

  -- AST Gen
  let f ← timeit "  AST Gen Time:     " (do
    let k' ← IO.rand 0 0
    pure (makeDeepChain (k + k'))
  )

  -- DAG Translation & SCC Collapse (The Kosaraju pass)
  let fAcyclic ← timeit "  DAG Compile Time: " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure f else pure f
    pure (compileAcyclic f')
  )

  -- Evaluation bounded by MCM K-Iteration Limit
  let fNormal ← timeit "  Lazy Reduce Time: " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure fAcyclic else pure fAcyclic
    pure (normalize f' 2000 0)
  )

  -- Force total evaluation hash
  let h ← timeit "  AST Hash Check:   " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure fNormal else pure fNormal
    pure (forceComb f')
  )

  IO.println s!"  AST Hash Result:  {h}\n"

def profileSaturatedCycle (k : Nat) : IO Unit := do
  IO.println s!"Saturated Paradoxical Cycle (V \\in V) [Depth={k} payload]:"

  let f ← timeit "  AST Gen Time:     " (do
    let k' ← IO.rand 0 0
    pure (makeSaturatedCycle (k + k'))
  )

  let fAcyclic ← timeit "  DAG Compile Time: " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure f else pure f
    pure (compileAcyclic f')
  )

  let fNormal ← timeit "  Lazy Reduce Time: " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure fAcyclic else pure fAcyclic
    -- The self-referential graph should halt cleanly at the iteration limit
    pure (normalize f' 5000 0)
  )

  let h ← timeit "  AST Hash Check:   " (do
    let f' ← if (← IO.rand 0 0) == 0 then pure fNormal else pure fNormal
    pure (forceComb f')
  )

  IO.println s!"  AST Hash Result:  {h}\n"

def main : IO Unit := do
  IO.println "Profiling Untyped Combinatory Engine...\n"

  IO.println "--- Test 1: Scaling Depth (Pure Topological Translation) ---"
  for k in [512, 1024, 2048, 4096] do
    profileComb k

  IO.println "\n--- Test 2: Saturated Paradoxical Recursion (MCM K-Iteration Bound) ---"
  for k in [128, 256, 512, 1024] do
    profileSaturatedCycle k
