import Init.Data.List.Basic

abbrev Var := String

inductive Formula where
  | eq : Var → Var → Formula
  | mem : Var → Var → Formula
  | neg : Formula → Formula
  | conj : Formula → Formula → Formula
  | disj : Formula → Formula → Formula
  | impl : Formula → Formula → Formula
  | univ : Var → Formula → Formula

def getFormulaVarsAux : Formula → List Var
  | Formula.eq x y => [x, y]
  | Formula.mem x y => [x, y]
  | Formula.neg p => getFormulaVarsAux p
  | Formula.conj p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.disj p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.impl p q => getFormulaVarsAux p ++ getFormulaVarsAux q
  | Formula.univ x p => x :: getFormulaVarsAux p
