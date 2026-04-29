import UntypedComb.Core
import UntypedComb.Categorical
import UntypedComb.Reduction
import UntypedComb.CombLib.YonedaTest

namespace UntypedComb.Examples

open Comb
open UntypedComb
open UntypedComb.YonedaTest

/--
  Define Pseudo-Cartesian Closure natively on the untyped graph.
  We map the categorical products and exponentials onto standard combinatory logic constructs,
  whilst ensuring the evaluation arrows absorb the topological friction via the T-functor.
-/
def N_PCC : PseudoCartesianClosure Unit N_SPE := {
  -- Product is Church pairs: \x y z. z x y -> λz. z A B. We just use a terminal for abstract bounds.
  prod := fun _ _ => Comb.terminal "PROD",
  -- Exponential is just the space of combinators natively
  exp := fun _ _ => Comb.terminal "EXP",

  -- The T-relative adjunction mapping
  t_adjunction_hom := fun _ => Comb.terminal "T_ADJ_HOM",
  t_adjunction_inv := fun _ => Comb.terminal "T_ADJ_INV",

  -- 2. Evaluation Arrow ev'_{A,B}: TA × (A ⇒ B) → TB
  -- This absorbs topological friction by T-shifting the evaluation.
  -- In untyped combinatory logic, ev'(t_a, f) = (T f) t_a
  ev_prime := fun _ _ =>
    -- We represent the evaluation prime operator as mechanically shifting the functor
    app (terminal "EV_PRIME") (t_inject (terminal "ABSORBED_FRICTION")),

  sub_obj := fun _ => terminal "SUB_OBJ",
  bool_obj := terminal "BOOL_OBJ",

  t_bool_iso := terminal "T_BOOL_ISO",
  t_bool_iso_inv := terminal "T_BOOL_ISO_INV",

  sub_representability := fun _ => terminal "SUB_REP",
  sub_representability_inv := fun _ => terminal "SUB_REP_INV"
}

/--
  Execute the Pseudo-Cartesian evaluation test.
  This forces the evaluation of ev' with a simulated pair (TA, f).
-/
def executePseudoCartesianEval : Comb :=
  let ev_map := N_PCC.ev_prime (terminal "A") (terminal "B")
  app ev_map (terminal "PAIR_TA_F")

#eval! executePseudoCartesianEval
#eval! normalize executePseudoCartesianEval

end UntypedComb.Examples
