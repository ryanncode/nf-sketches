import ParseStrat.ITP
import NfValidate

open ITP
open Formula
open Atomic

/-!
# Component 3: Tactical Example Programs

These synthetic theorem proving scenarios independently invoke and chain
the 13 newly integrated Monist tactics to verify their native execution
and AST transformations inside Lean 4.
-/

-- Example 1: Testing DAG Isomorphism via `refl` and `have`
-- Shows that if A = B and B = C, `refl` on A = C succeeds via Kosaraju SCC flattening.
def exampleRefl : Except String ProofState := do
  let start : ProofState := [{
    ctx := [("H1", atom (eq (Var.free "A") (Var.free "B"))),
            ("H2", atom (eq (Var.free "B") (Var.free "C")))],
    target := atom (eq (Var.free "A") (Var.free "C"))
  }]
  reflTactic start

-- Example 2: Testing `stratify` and `step`
-- Creates a valid stratifiable formula and runs the geometric oracle.
def exampleStratify : Except String ProofState := do
  let start : ProofState := [{
    ctx := [],
    target := atom (mem (Var.free "x") (Var.free "y"))
  }]
  let s1 ← stepTactic start
  stratifyTactic s1

-- Example 3: Testing `deff`, `simp`, and `collapse_loop`
-- Tests macro binding, Double-Negation/DNF reduction, and triggering mid-proof SCC contraction.
def exampleSimpLoop : Except String ProofState := do
  let start : ProofState := [{
    ctx := [],
    target := neg (neg (atom (mem (Var.free "x") (Var.free "y"))))
  }]
  let s1 ← deffTactic "MyMacro" (atom (mem (Var.free "x") (Var.free "y"))) start
  let s2 ← simpTactic s1
  collapseLoopTactic s2

-- Example 4: Testing `schonfinkel` and `elevate`
-- Elevates variables via the T-functor and dynamically compiles to SKI combinator topology.
def exampleSchonfinkel : Except String ProofState := do
  let start : ProofState := [{
    ctx := [],
    target := univ "x" "scope" (atom (mem (Var.bound 0) (Var.free "y")))
  }]
  let s1 ← elevateTactic start
  schonfinkelTactic s1

-- Example 5: Testing `rewrite`, `focus_hyp`, `defer`, `cut`
-- Exercises standard ITP queue navigation and AST substitutions.
def exampleSurgery : Except String ProofState := do
  let start : ProofState := [{
    ctx := [("EqHyp", atom (eq (Var.free "A") (Var.free "B"))),
            ("Irrelevant", atom (eq (Var.free "X") (Var.free "Y")))],
    target := atom (mem (Var.free "A") (Var.free "C"))
  }]
  let s1 ← focusHypTactic "EqHyp" start
  let s2 ← cutTactic (atom (mem (Var.free "B") (Var.free "C"))) s1
  let s3 ← deferTactic s2
  rewriteTactic "EqHyp" s3

def runAllExamples : IO Unit := do
  IO.println "--- Component 3 Tactical Examples ---"
  
  IO.print "exampleRefl (SCC DAG Isomorphism): "
  match exampleRefl with
  | Except.ok _ => IO.println "SUCCESS"
  | Except.error e => IO.println s!"FAILED: {e}"
  
  IO.print "exampleStratify (Oracle & Trace): "
  match exampleStratify with
  | Except.ok _ => IO.println "SUCCESS"
  | Except.error e => IO.println s!"FAILED: {e}"

  IO.print "exampleSimpLoop (Macro & Contraction): "
  match exampleSimpLoop with
  | Except.ok _ => IO.println "SUCCESS"
  | Except.error e => IO.println s!"FAILED: {e}"

  IO.print "exampleSchonfinkel (T-Functor & SKI): "
  match exampleSchonfinkel with
  | Except.ok _ => IO.println "SUCCESS"
  | Except.error e => IO.println s!"FAILED: {e}"

  IO.print "exampleSurgery (Rewrite & Queue): "
  match exampleSurgery with
  | Except.ok _ => IO.println "SUCCESS"
  | Except.error e => IO.println s!"FAILED: {e}"
