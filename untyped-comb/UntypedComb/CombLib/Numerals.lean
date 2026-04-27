import UntypedComb.Core
import UntypedComb.Reduction

namespace UntypedComb.Numerals

open Comb

/-- B combinator (composition) = S (K S) K -/
def B : Comb := app (app S (app K S)) K

/-- Church numeral 0 = K I -/
def zero : Comb := app K I

/-- Church numeral 1 = I -/
def one : Comb := I

/-- Church numeral 2 = S B I = S (S (K S) K) I -/
def two : Comb := app (app S B) I

/-- Successor = \n f x. f (n f x) = S B -/
def succ : Comb := app S B

/-- Addition = \m n. m Succ n = S I (K Succ) -/
def add : Comb := app (app S I) (app K succ)

/-- Multiplication = \m n. m (n f) x = B -/
def mult : Comb := B

end UntypedComb.Numerals
