import UntypedComb.Core
import UntypedComb.Reduction
import UntypedComb.CombLib.Booleans
import UntypedComb.CombLib.Numerals
import UntypedComb.CombLib.Recursion

namespace UntypedComb.CombLib.Tests

open Comb
open UntypedComb.Booleans
open UntypedComb.Numerals
open UntypedComb.Recursion

/-- Helper to test whether an expression reduces to an expected normal form. -/
def testReduction (term expected : Comb) : Bool :=
  normalize term == normalize expected

/-- Helper to test whether two Church numerals are extensionally equivalent by applying them to dummy variables. -/
def testNumeralEq (n m : Comb) : Bool :=
  normalize (app (app n (var "f")) (var "x")) == normalize (app (app m (var "f")) (var "x"))

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
-- The tests demonstrate the basic building blocks without topological guards.
-- We can test one step of reduction manually if needed, but for now we skip infinite loops.

end UntypedComb.CombLib.Tests
