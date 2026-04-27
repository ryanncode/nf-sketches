import UntypedComb.Core
import UntypedComb.CombLib.Recursion
import UntypedComb.CombLib.Lists

namespace UntypedComb.CombLib.SelfModels

open Comb
open UntypedComb.CombLib.Lists

/--
The universal set V containing itself natively (V ∈ V).
We define V as an infinite list where every element is V itself.
Using the Y combinator:
`V = Y (\v. cons v nil)` -- wait, if V contains everything, a simple self-reference is `V = cons V V` or `V = cons V nil` (a set containing only itself, like a Quine atom).
Let's model an atom `Ω = {Ω}`.
`omegaSet = Y (\x. cons x nil)`
-/
def buildQuineAtom : Comb :=
  -- \x. cons x nil
  -- In combinators, cons x nil = app (app cons x) nil
  -- However `cons` in `Lists.lean` is a Lean function `Comb -> Comb -> Comb`.
  -- We need the combinator form of `cons`.
  -- `CONS = \x y z. z x y = S (S (K S) (S (K (S I)) (K K))) (K I)` (Standard derivation)
  let CONS := app (app S (app (app S (app K S)) (app (app S (app K (app S I))) (app K K)))) (app K I)
  let NIL := nil
  -- \x. CONS x NIL = S (S (K CONS) I) (K NIL)
  let f := app (app S (app (app S (app K CONS)) I)) (app K NIL)

  -- Apply Y combinator to f
  app UntypedComb.Recursion.Y f

/--
A model of the universal set V natively expanding out to contain unreduced copies of its own topology.
`V = Y (\v. cons v v)` -- an infinite binary tree where every node is identical to the root.
-/
def buildUniversalSet : Comb :=
  let CONS := app (app S (app (app S (app K S)) (app (app S (app K (app S I))) (app K K)))) (app K I)
  -- \v. CONS v v = S CONS I
  let f := app (app S CONS) I

  -- Apply Y to f
  app UntypedComb.Recursion.Y f

end UntypedComb.CombLib.SelfModels
