import UntypedComb.Core
import UntypedComb.CombLib.Booleans
import UntypedComb.CombLib.Recursion

namespace UntypedComb.CombLib.Lists

open Comb

/--
Church-encoded Pairs (Cons cells).
`pair = \x y z. z x y`
In combinators, given x and y, `pair x y = S (S I (K x)) (K y)`
-/
def cons (x y : Comb) : Comb :=
  app (app S (app (app S I) (app K x))) (app K y)

/--
Extract the head of a list.
`head = \p. p tru`
-/
def head : Comb :=
  app (app S I) (app K UntypedComb.Booleans.tru)

/--
Extract the tail of a list.
`tail = \p. p fls`
-/
def tail : Comb :=
  app (app S I) (app K UntypedComb.Booleans.fls)

/--
Nil (empty list). Represents an empty boundary.
`nil = \z. tru`
-/
def nil : Comb :=
  app K UntypedComb.Booleans.tru

/--
Checks if a list is empty.
`isNil = \p. p (\x y. fls)`
-/
def isNil : Comb :=
  app (app S I) (app K (app K (app K UntypedComb.Booleans.fls)))

end UntypedComb.CombLib.Lists
