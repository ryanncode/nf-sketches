import UntypedComb.Core
import UntypedComb.CombLib.Booleans
import UntypedComb.CombLib.Lists
import UntypedComb.CombLib.Recursion
import UntypedComb.CombLib.Numerals

namespace UntypedComb.CombLib.Cardinals

open Comb

/--
Native Cardinal Arithmetic without the Axiom of Choice.
In NF, we can define the cardinality of a set `A` as the set of all sets equinumerous to `A`.
`|A| = { B | A ~ B }`.

We can define an equivalence relation `~` (equinumerous) without relying on well-ordering.
If `A` and `B` are sets (predicates), `A ~ B` means there exists a bijection between them.
For the logic engine, transfinite cardinals are just nodes in the DAG.
We define a cardinal addition operator `+`.
`|A| + |B| = |A ∪ B|` (assuming A and B are disjoint).
-/

-- Disjoint Union
-- A ⊔ B = \p. p (\tag val. tag A B val)
-- Compiled to combinators: S I (K (S (S I (K A)) (K B)))
def disjointUnion (A B : Comb) : Comb :=
  app (app S I) (app K (app (app S (app (app S I) (app K A))) (app K B)))

/--
Cardinal Addition Operator
Takes two cardinals, constructs their disjoint union, and abstracts to the equivalence class.
The abstraction requires a type shift, modeled by the t_inject functor.
-/
def cardAdd (A B : Comb) : Comb :=
  t_inject (disjointUnion A B)

/-- A placeholder for Cardinal Multiplication -/
def cardMul : Comb :=
  var "Card_Mul"

/--
Pure combinator for Cons.
\x y z. z x y
-/
def consComb : Comb :=
  app (app S (app K S)) (app (app S (app K K)) (app (app S (app K S)) (app (app S (app K (app S I))) K)))

/--
The infinite set generator: \f n. cons n (f (succ n))
Abstracted into Combinators:
S (K (S cons)) (S (S (K S) K) (K succ))
-/
def infStreamGen : Comb :=
  app (app S (app K (app S consComb)))
      (app (app S (app (app S (app K S)) K))
           (app K Numerals.succ))

/--
The canonical countably infinite set (a stream of numerals).
Built using the Y combinator to saturated infinite recursion.
-/
def infSet : Comb :=
  app (app Recursion.Y infStreamGen) Numerals.zero

/--
Aleph_0: The set of all countably infinite sets.
Represented here by anchoring to our canonical stream and elevating
its topological type with t_inject to model the cardinality abstraction.
-/
def aleph0 : Comb :=
  t_inject infSet

end UntypedComb.CombLib.Cardinals
