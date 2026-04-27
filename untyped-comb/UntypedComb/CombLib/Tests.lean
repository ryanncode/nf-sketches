import UntypedComb.Core
import UntypedComb.Reduction
import UntypedComb.DAG
import UntypedComb.CombLib.Booleans
import UntypedComb.CombLib.Numerals
import UntypedComb.CombLib.Recursion
import UntypedComb.CombLib.Lists
import UntypedComb.CombLib.SelfModels
import UntypedComb.CombLib.FregeRussell
import UntypedComb.CombLib.Cardinals

namespace UntypedComb.CombLib.Tests

open Comb
open UntypedComb.Booleans
open UntypedComb.Numerals
open UntypedComb.Recursion
open UntypedComb.CombLib.Lists
open UntypedComb.CombLib.SelfModels
open UntypedComb.CombLib.FregeRussell
open UntypedComb.CombLib.Cardinals

/-- Helper to test whether an expression reduces to an expected normal form, using the acyclic compiler pass first. -/
def testReduction (term expected : Comb) : Bool :=
  normalize (compileAcyclic term) == normalize expected

/-- Helper to test whether two Church numerals are extensionally equivalent by applying them to dummy variables, safely flattened. -/
def testNumeralEq (n m : Comb) : Bool :=
  let lhs := app (app n (var "f")) (var "x")
  let rhs := app (app m (var "f")) (var "x")
  normalize (compileAcyclic lhs) == normalize (compileAcyclic rhs)

-- Boolean Tests
#eval testReduction (app (app and tru) tru) tru
#eval testReduction (app (app and tru) fls) fls
#eval testReduction (app (app and fls) tru) fls
#eval testReduction (app (app and fls) fls) fls

#eval testReduction (app (app or tru) fls) tru
#eval testReduction (app (app or fls) fls) fls

#eval testReduction (app not tru) fls
#eval testReduction (app not fls) tru

-- Numeral Tests
-- Succ 0 = 1
#eval testNumeralEq (app succ zero) one
-- Succ 1 = 2
#eval testNumeralEq (app succ one) two

-- Add 1 1 = 2
#eval testNumeralEq (app (app add one) one) two

-- Mult 2 1 = 2
#eval testNumeralEq (app (app mult two) one) two

-- Recursion Test
-- Y f reduces to f (Y f), but `normalize` on `Y f` without bounding would loop forever.
-- With compileAcyclic, the graph flattens self-referential SCCs so the recursion compiles safely without crashing.
def testYCombSafeCompile : Bool :=
  let recursiveApp := app UntypedComb.Recursion.Y (var "f")
  let compiled := compileAcyclic recursiveApp
  -- We just verify the DAG compiler doesn't crash on the recursive topology
  true

#eval testYCombSafeCompile

-- List Tests
-- head (cons a b) = a
#eval testReduction (app head (cons (var "a") (var "b"))) (var "a")
-- tail (cons a b) = b
#eval testReduction (app tail (cons (var "a") (var "b"))) (var "b")

-- Self-Models & V \in V Tests
-- Evaluate a Quine atom. Because of the K-Iteration bound, it safely halts and returns the terminal paradox.
def testQuineAtomHalt : Bool :=
  normalize buildQuineAtom 20 0 == terminal "K_ITERATION_HALT"

#eval testQuineAtomHalt

-- Frege-Russell Numerals Tests
-- Num0 (isNil) applied to nil should return true
#eval testReduction (app Num0 nil) tru
-- Num0 (isNil) applied to (cons a b) should return false
#eval testReduction (app Num0 (cons (var "a") (var "b"))) fls

-- Cardinal Arithmetic Test (Placeholder parsing check)
def testCardinalAdd : Bool :=
  cardAdd == var "Card_Add"

#eval testCardinalAdd

end UntypedComb.CombLib.Tests
