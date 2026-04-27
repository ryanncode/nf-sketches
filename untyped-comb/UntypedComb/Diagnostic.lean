import UntypedComb.Core
import UntypedComb.Topological

namespace UntypedComb

/--
A basic mock type-checker/weight-tracker for combinatorial logic in a weak stratification environment.
We assign integer levels to terms. The application `F X` requires `F` to map from the level of `X`.
If `F` creates a function type, it fundamentally shifts the integer levels.
-/
partial def distanceMap (t : Comb) : Option Int :=
  match t with
  | Comb.I => some 0
  | Comb.K =>
    -- K = λx. λy. x
    -- K forces the type of the result to jump topological bounds
    -- because x drops y's context entirely.
    -- We assign it a base shift of 1 to simulate its stratification boundary.
    some 1
  | Comb.S => some 2
  | Comb.U => some 0
  | Comb.var _ => some 0
  | Comb.t_inject x =>
    -- T-operator mechanically shifts the implicit type level of a function up by one.
    match distanceMap x with
    | some w => some (w + 1)
    | none => none
  | Comb.app f x =>
    match distanceMap f, distanceMap x with
    | some wf, some wx =>
      -- In a naive typed system without T-weaking, applying mismatched levels fails.
      -- But here we return the max or the expected level of the result.
      -- The application distance is essentially the function's level minus 1, but we
      -- can just track the current cumulative weight shift.
      if wf == wx then some wf
      else none -- Misalignment that needs to be T-weaked
    | _, _ => none

/--
The `reduceCut` equivalent for the untyped combinatorial calculus.
It evaluates a topological execution path, intentionally looking for where
unstratified combinatorial structures collide with extensional identity.
-/
def reduceCutCombinator (term : Comb) : EvaluationResult :=
  match distanceMap term with
  | none => EvaluationResult.ExtensionalityCollision [("Misaligned_Levels", -1)]
  | some _ => EvaluationResult.Normalized term

end UntypedComb
