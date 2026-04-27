import UntypedComb.Core
import UntypedComb.Topological

namespace UntypedComb

/--
A basic mock type-checker/weight-tracker for combinatorial logic in a weak stratification environment.
We assign integer levels to terms. The application `F X` requires `F` to map from the level of `X`.
If `F` creates a function type, it fundamentally shifts the integer levels.
-/
def checkTypeShift (t : Comb) : Option Int :=
  match t with
  | Comb.I => some 0
  | Comb.K =>
    -- K = λx. λy. x
    -- K forces the type of the result to jump topological bounds
    -- because x drops y's context entirely.
    -- In NF, this causes a +1 or +2 level misalignment depending on the structure.
    -- We'll return none here for un-T-weaked K to simulate the breakdown.
    none
  | Comb.S => some 0
  | Comb.U => some 0
  | Comb.var _ => some 0
  | Comb.t_inject x =>
    -- T-operator mechanically shifts the implicit type level of a function up by one.
    match checkTypeShift x with
    | some w => some (w + 1)
    | none => none
  | Comb.app f x =>
    match checkTypeShift f, checkTypeShift x with
    | some wf, some wx =>
      -- In a naive typed system without T-weaking, applying mismatched levels fails.
      if wf == wx then some wf else none
    | _, _ => none

/--
The `reduceCut` equivalent for the untyped combinatorial calculus.
It evaluates a topological execution path, intentionally looking for where
unstratified combinatorial structures (like K) collide with extensional identity.
-/
def reduceCutCombinator (term : Comb) : EvaluationResult :=
  -- If the term's integer weights misalign natively (e.g. standard K combinator without T)
  -- we map this physical constraint failure as an Extensionality Collision.
  match checkTypeShift term with
  | none => EvaluationResult.ExtensionalityCollision [("Misaligned_Levels", -1)]
  | some _ => EvaluationResult.Normalized term

end UntypedComb
