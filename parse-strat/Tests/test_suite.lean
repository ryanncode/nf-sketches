import NfValidate
import ParseStrat

/-!
# ParseStrat: Automated Test Suite

This module provides an automated test suite for the `nf-validate` strict
stratification engine. It verifies the detection of topological cycles,
demonstrating the algorithmic boundaries where strict global leveling
mathematically halts.
-/

open Formula

-- Helper functions to assert the result type during compilation
def isSuccess (res : StratificationResult) : Bool :=
  match res with
  | StratificationResult.success _ => true
  | StratificationResult.failure _ _ => false

def isFailure (res : StratificationResult) : Bool :=
  not (isSuccess res)

def assertTest (name : String) (f : Formula) (expectSuccess : Bool) : String :=
  match evaluateFullFormula f with
  | StratificationResult.success witness =>
      if expectSuccess then
        s!"[PASS] {name}\n  Result: Stratifiable\n  Witness: {formatWitness witness}\n"
      else
        s!"[FAIL] {name}\n  Expected Unstratifiable, but found valid assignment:\n  Witness: {formatWitness witness}\n"

  | StratificationResult.failure cycle edges =>
      if not expectSuccess then
        let cycleDetail := formatDetailedCycleSandbox cycle edges
        s!"[PASS] {name}\n  Result: Unstratifiable\n  {cycleDetail}\n"
      else
        let cycleDetail := formatDetailedCycleSandbox cycle edges
        s!"[FAIL] {name}\n  Expected Stratifiable, but found contradiction:\n  {cycleDetail}\n"

-- Override mem and eq to use Var.free
def mem (x y : String) : Formula := Formula.atom (Atomic.mem (Var.free x) (Var.free y))
def eq (x y : String) : Formula := Formula.atom (Atomic.eq (Var.free x) (Var.free y))
def univ_str (x : String) (f : Formula) : Formula := Formula.univ 0 x f

--------------------------------------------------------------------------------
-- 1. Base Atomic Stratification
--------------------------------------------------------------------------------
def test_base_mem : Formula := mem "x" "y"
def test_base_eq : Formula := eq "x" "y"

--------------------------------------------------------------------------------
-- 2. Transitive Type Shifts and Equality Merging
--------------------------------------------------------------------------------
-- x ∈ y ∧ y ∈ z ∧ z ∈ w (Valid sequential typing)
def test_transitive : Formula :=
  conj (mem "x" "y") (conj (mem "y" "z") (mem "z" "w"))

--------------------------------------------------------------------------------
-- 3. DNF Branching and Partial Success
--------------------------------------------------------------------------------
-- (x ∈ y ∧ y ∈ z) ∨ (x ∈ x)
-- Stratifiable because the left branch contains no negative cycles.
def test_disj_success : Formula :=
  disj (conj (mem "x" "y") (mem "y" "z")) (mem "x" "x")

--------------------------------------------------------------------------------
-- 4. Implication and Negation Semantics
--------------------------------------------------------------------------------
-- ¬(x ∈ y ∧ y ∈ z)
-- Tests pushNeg and De Morgan's laws: ¬(x ∈ y) ∨ ¬(y ∈ z). Both branches stratifiable.
def test_neg_conj : Formula :=
  neg (conj (mem "x" "y") (mem "y" "z"))

-- x ∈ y → y ∈ z
-- Tests implication expansion: ¬(x ∈ y) ∨ (y ∈ z). Both branches stratifiable.
def test_impl : Formula :=
  impl (mem "x" "y") (mem "y" "z")

--------------------------------------------------------------------------------
-- 5. Universal Quantification
--------------------------------------------------------------------------------
-- ∀x, x ∈ y
-- The validator should extract constraints bypassing the quantifier.
def test_univ : Formula :=
  univ_str "x" (mem "x" "y")

--------------------------------------------------------------------------------
-- 6. Total Failure (All DNF Branches Unstratifiable)
--------------------------------------------------------------------------------
-- (x ∈ x) ∨ (y ∈ z ∧ z ∈ y)
-- Both the left branch and right branch contain cycles. Must return failure.
def paradox_all_fail : Formula :=
  disj (mem "x" "x") (conj (mem "y" "z") (mem "z" "y"))

--------------------------------------------------------------------------------
-- 7. Known Paradoxes (Cyclical Constraints)
--------------------------------------------------------------------------------
-- x ∈ x (Russell's paradox base case)
def paradox_russell : Formula :=
  mem "x" "x"

-- x ∈ y ∧ y ∈ x (2-cycle)
def paradox_2cycle : Formula :=
  conj (mem "x" "y") (mem "y" "x")

-- x ∈ y ∧ y ∈ z ∧ z ∈ x (3-cycle)
def paradox_3cycle : Formula :=
  conj (mem "x" "y") (conj (mem "y" "z") (mem "z" "x"))

-- x = y ∧ y ∈ x (Equality constraint cycle)
def paradox_eq_cycle : Formula :=
  conj (eq "x" "y") (mem "y" "x")

--------------------------------------------------------------------------------
-- 8. Soundness Test (Dynamic Re-leveling)
--------------------------------------------------------------------------------
-- Tests deep AST scope partitioning as verified in the soundness proof.
-- Formula: (x ∈ y) ∧ ∀w(y ∈ w) ∧ ∀v(v ∈ x)
-- Demonstrates successful isolation of distinct scopes (0, 1, 2) without
-- unintended variable collision or canonical contradiction.
def test_dynamic_soundness : Formula :=
  conj (mem "x" "y")
    (conj (Formula.univ 1 "w" (Formula.atom (Atomic.mem (Var.free "y") (Var.bound 0))))
          (Formula.univ 2 "v" (Formula.atom (Atomic.mem (Var.bound 0) (Var.free "x")))))

--------------------------------------------------------------------------------
-- Execution and Verification Assertions
--------------------------------------------------------------------------------

#eval! IO.print (assertTest "Base Mem" test_base_mem true)
#eval! IO.print (assertTest "Base Eq" test_base_eq true)
#eval! IO.print (assertTest "Transitive Shift" test_transitive true)
#eval! IO.print (assertTest "DNF Partial Success" test_disj_success true)
#eval! IO.print (assertTest "Negation Push" test_neg_conj true)
#eval! IO.print (assertTest "Implication" test_impl true)
#eval! IO.print (assertTest "Universal" test_univ true)

#eval! IO.print (assertTest "DNF Total Failure" paradox_all_fail false)
#eval! IO.print (assertTest "Russell Paradox" paradox_russell false)
#eval! IO.print (assertTest "2-Cycle" paradox_2cycle false)
#eval! IO.print (assertTest "3-Cycle" paradox_3cycle false)
#eval! IO.print (assertTest "Equality Cycle" paradox_eq_cycle false)

#eval! IO.print (assertTest "Dynamic Soundness Partitioning" test_dynamic_soundness true)

def runReplTest (name : String) (file : String) : IO Unit := do
  let out ← IO.Process.output { cmd := "sh", args := #["-c", s!"lake exe parse-strat < {file}"] }
  if out.exitCode == 0 then
    IO.println s!"[PASS] REPL Test: {name}"
  else
    IO.println s!"[FAIL] REPL Test: {name}\n{out.stderr}\n{out.stdout}"

#eval! runReplTest "SC Stability" "Tests/test_sc_stability.txt"
#eval! runReplTest "Cut/Focus/Defer" "Tests/test_cut_focus_defer.txt"
#eval! runReplTest "Weaponized Cut" "Tests/test_weaponized_cut.txt"
#eval! runReplTest "Strategic Cut" "Tests/test_strategic_cut.txt"
#eval! runReplTest "Kuratowski Bounds" "Tests/test_kuratowski_bounds.txt"
#eval! runReplTest "Quine Pair Injectivity" "Tests/test_q_injective.txt"
#eval! runReplTest "Strict Subset Asymmetry" "Tests/test_strict_subset_asym.txt"
#eval! runReplTest "Distributivity (L/R)" "Tests/test_distributivity_lr.txt"
#eval! runReplTest "Subset Transitivity" "Tests/test_subset_transitivity.txt"
