import UntypedComb.Core
import UntypedComb.Reduction
import UntypedComb.CombLib.Numerals

namespace UntypedComb.Recursion

open Comb

/-- Self-application combinator \x. x x = S I I -/
def M : Comb := app (app S I) I

/--
The Y combinator allows for unrestricted recursion.
Y = \f. (\x. f (x x)) (\x. f (x x))
In SKI: Y = S (K (S I I)) (S (S (K S) K) (K (S I I)))
Using B = S (K S) K: Y = S (K M) (S B (K M))
-/
def Y : Comb :=
  app (app S (app K M)) (app (app S UntypedComb.Numerals.B) (app K M))

end UntypedComb.Recursion
