import UntypedComb.Core

namespace UntypedComb

/--
A single step of β-reduction for standard combinators.
This operates purely via term rewriting.
-/
def reduceStep : Comb → Option Comb
  -- K x y => x
  | Comb.app (Comb.app Comb.K x) _ => some x
  -- S x y z => x z (y z)
  | Comb.app (Comb.app (Comb.app Comb.S x) y) z => some (Comb.app (Comb.app x z) (Comb.app y z))
  -- I x => x
  | Comb.app Comb.I x => some x
  -- U f g x => f x |^x g x (NAND placeholder reduction)
  -- For now, we leave U unreduced unless we implement the specific boolean logic mappings.

  -- Structural reductions for applications
  | Comb.app f x =>
    match reduceStep f with
    | some f' => some (Comb.app f' x)
    | none =>
      match reduceStep x with
      | some x' => some (Comb.app f x')
      | none => none

  -- T-shift reduction (placeholder for now, T x evaluates the shifted term)
  | Comb.t_inject x =>
    match reduceStep x with
    | some x' => some (Comb.t_inject x')
    | none => none

  | _ => none

/--
Evaluates a combinator term to its normal form by repeatedly applying `reduceStep`.
-/
partial def normalize (t : Comb) : Comb :=
  match reduceStep t with
  | some t' => normalize t'
  | none => t

end UntypedComb
