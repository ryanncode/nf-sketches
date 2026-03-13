import NfValidate
import Main

open Formula

-- Helper functions to assert the result type during compilation
def isSuccess (res : StratificationResult) : Bool :=
  match res with
  | StratificationResult.success _ => true
  | StratificationResult.failure _ _ => false

def isFailure (res : StratificationResult) : Bool :=
  not (isSuccess res)

-- Override mem and eq to use Var.free
def mem (x y : String) : Formula := Formula.atom (Atomic.mem (Var.free x) (Var.free y))
def eq (x y : String) : Formula := Formula.atom (Atomic.eq (Var.free x) (Var.free y))
def univ_str (x : String) (f : Formula) : Formula := Formula.univ x f

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
-- Execution and Verification Assertions
--------------------------------------------------------------------------------

#eval if isSuccess (evaluateFullFormula test_base_mem) then "Pass: Base Mem" else "Fail: Base Mem"
#eval if isSuccess (evaluateFullFormula test_base_eq) then "Pass: Base Eq" else "Fail: Base Eq"
#eval if isSuccess (evaluateFullFormula test_transitive) then "Pass: Transitive Shift" else "Fail: Transitive Shift"
#eval if isSuccess (evaluateFullFormula test_disj_success) then "Pass: DNF Partial Success" else "Fail: DNF Partial Success"
#eval if isSuccess (evaluateFullFormula test_neg_conj) then "Pass: Negation Push" else "Fail: Negation Push"
#eval if isSuccess (evaluateFullFormula test_impl) then "Pass: Implication" else "Fail: Implication"
#eval if isSuccess (evaluateFullFormula test_univ) then "Pass: Universal" else "Fail: Universal"

#eval if isFailure (evaluateFullFormula paradox_all_fail) then "Pass: DNF Total Failure" else "Fail: DNF Total Failure"
#eval if isFailure (evaluateFullFormula paradox_russell) then "Pass: Russell Paradox" else "Fail: Russell Paradox"
#eval if isFailure (evaluateFullFormula paradox_2cycle) then "Pass: 2-Cycle" else "Fail: 2-Cycle"
#eval if isFailure (evaluateFullFormula paradox_3cycle) then "Pass: 3-Cycle" else "Fail: 3-Cycle"
#eval if isFailure (evaluateFullFormula paradox_eq_cycle) then "Pass: Equality Cycle" else "Fail: Equality Cycle"
