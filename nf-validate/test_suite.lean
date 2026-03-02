import NfValidate

open Formula

-- Valid stratified sets

-- x ∈ y
def test1 : Formula := mem "x" "y"
#eval evaluateStratification test1

-- x ∈ y ∧ y ∈ z
def test2 : Formula := conj (mem "x" "y") (mem "y" "z")
#eval evaluateStratification test2

-- x = y ∧ y ∈ z
def test3 : Formula := conj (eq "x" "y") (mem "y" "z")
#eval evaluateStratification test3

-- x ∈ y ∨ x ∈ x  (The first branch is stratifiable, so the whole formula should be)
-- Wait, `evaluateStratification` uses `evaluateClause` which does not do DNF reduction.
-- `evaluateFullFormula` does DNF reduction! Let's test `evaluateFullFormula`.
#eval evaluateFullFormula (disj (mem "x" "y") (mem "x" "x"))

-- Unstratifiable paradoxes

-- x ∈ x (Russell's paradox base case)
def paradox1 : Formula := mem "x" "x"
#eval evaluateStratification paradox1

-- x ∈ y ∧ y ∈ x (2-cycle)
def paradox2 : Formula := conj (mem "x" "y") (mem "y" "x")
#eval evaluateStratification paradox2

-- x ∈ y ∧ y ∈ z ∧ z ∈ x (3-cycle)
def paradox3 : Formula := conj (mem "x" "y") (conj (mem "y" "z") (mem "z" "x"))
#eval evaluateStratification paradox3

-- x = y ∧ y ∈ x
def paradox4 : Formula := conj (eq "x" "y") (mem "y" "x")
#eval evaluateStratification paradox4

-- Check that `#eval` outputs the expected `StratificationResult.success` or `failure`.
-- Since `#eval` just prints to stdout during compilation, we can also write a simple
-- function to assert the result type.

def isSuccess (res : StratificationResult) : Bool :=
  match res with
  | StratificationResult.success _ => true
  | StratificationResult.failure _ _ => false

def isFailure (res : StratificationResult) : Bool :=
  not (isSuccess res)

-- Assertions
#eval if isSuccess (evaluateFullFormula test1) then "Pass" else "Fail"
#eval if isSuccess (evaluateFullFormula test2) then "Pass" else "Fail"
#eval if isSuccess (evaluateFullFormula test3) then "Pass" else "Fail"

#eval if isFailure (evaluateFullFormula paradox1) then "Pass" else "Fail"
#eval if isFailure (evaluateFullFormula paradox2) then "Pass" else "Fail"
#eval if isFailure (evaluateFullFormula paradox3) then "Pass" else "Fail"
#eval if isFailure (evaluateFullFormula paradox4) then "Pass" else "Fail"
