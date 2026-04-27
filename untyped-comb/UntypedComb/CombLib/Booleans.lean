import UntypedComb.Core
import UntypedComb.Reduction

namespace UntypedComb.Booleans

open Comb

/-- True = K -/
def tru : Comb := K

/-- False = K I -/
def fls : Comb := app K I

/-- NOT = \p. p False True = S (S I (K fls)) (K tru) -/
def not : Comb :=
  app (app S (app (app S I) (app K fls))) (app K tru)

/-- AND = \p q. p q p = S (S (K S) I) K -/
def and : Comb :=
  app (app S (app (app S (app K S)) I)) K

/-- OR = \p q. p p q = S (S (K S) (S (K K) (S I I))) (K I) -/
def or : Comb :=
  app (app S (app (app S (app K S)) (app (app S (app K K)) (app (app S I) I)))) (app K I)

end UntypedComb.Booleans
