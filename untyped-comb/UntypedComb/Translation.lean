import UntypedComb.Core
import UntypedComb.Topological
import UntypedComb.CombLib.Booleans
import NfValidate

-- We do not open NfValidate as a namespace since it's at the top level in NfValidate.lean

namespace UntypedComb

def translateVar : Var → Comb
  | Var.free s => Comb.var s
  | Var.bound n => Comb.var s!"_{n}"

-- We will build Church encodings for logic
def trueComb : Comb := Booleans.tru
def falseComb : Comb := Booleans.fls
def notComb : Comb := Booleans.not
def andComb : Comb := Booleans.and
def orComb : Comb := Booleans.or

-- Missing combinators: eq, mem, forall, etc. For now we use abstract vars.
def eqComb : Comb := Comb.var "EQ"
def memComb : Comb := Comb.var "MEM"
def qpairComb : Comb := Comb.var "QPAIR"
def qproj1Comb : Comb := Comb.var "QPROJ1"
def qproj2Comb : Comb := Comb.var "QPROJ2"

def translateAtomic : Atomic → Comb
  | Atomic.eq x y => Comb.app (Comb.app eqComb (translateVar x)) (translateVar y)
  | Atomic.mem x y => Comb.app (Comb.app memComb (translateVar x)) (translateVar y)
  | Atomic.qpair p x y => Comb.app (Comb.app (Comb.app qpairComb (translateVar p)) (translateVar x)) (translateVar y)
  | Atomic.qproj1 z p => Comb.app (Comb.app qproj1Comb (translateVar z)) (translateVar p)
  | Atomic.qproj2 z p => Comb.app (Comb.app qproj2Comb (translateVar z)) (translateVar p)
  | Atomic.app z u v => Comb.app (Comb.app (Comb.app (Comb.var "APP") (translateVar z)) (translateVar u)) (translateVar v)
  | Atomic.lam z x t => Comb.app (Comb.app (Comb.app (Comb.var "LAM") (translateVar z)) (translateVar x)) (translateVar t)

-- Abstracting over variables is hard in combinatory logic natively without bracket abstraction algorithm,
-- but we map the structure for now since we are focusing on topological bounds checking.
def translateFormula : Formula → Comb
  | Formula.atom a => translateAtomic a
  | Formula.neg f => Comb.app notComb (translateFormula f)
  | Formula.conj f1 f2 => Comb.app (Comb.app andComb (translateFormula f1)) (translateFormula f2)
  | Formula.disj f1 f2 => Comb.app (Comb.app orComb (translateFormula f1)) (translateFormula f2)
  | Formula.impl f1 f2 => Comb.app (Comb.app (Comb.var "IMPL") (translateFormula f1)) (translateFormula f2)
  | Formula.univ _ s f => Comb.app (Comb.app (Comb.var "UNIV") (Comb.var s)) (translateFormula f)
  | Formula.comp _ s f => Comb.app (Comb.app (Comb.var "COMP") (Comb.var s)) (translateFormula f)

-- Extract genuine integer weights from the StratificationWitness
def getWeightFromWitness (w : StratificationWitness) (scope : Nat) (v : Var) : Int :=
  lookupVarWeight (lookupScope w scope) v

-- A dynamic distance map that uses the witness to provide live bounds from the Bellman-Ford matrix.
def buildDynamicDistanceMap (w : StratificationWitness) (scope : Nat) : Comb → Option Int
  | Comb.var s =>
      if s.startsWith "_" then
        -- it's a bound variable like _0
        let n := (s.drop 1).toNat!
        some (getWeightFromWitness w scope (Var.bound n))
      else
        some (getWeightFromWitness w scope (Var.free s))
  | Comb.t_inject c =>
      match buildDynamicDistanceMap w scope c with
      | some w_c => some (w_c + 1)
      | none => none
  | Comb.app f x =>
      -- In our simple untyped evaluator, we'll try to get weights of the children.
      match buildDynamicDistanceMap w scope f, buildDynamicDistanceMap w scope x with
      | some wf, some _ => some wf -- just returning the function's weight for the app
      | some wf, none => some wf
      | none, some wx => some wx
      | none, none => none
  | _ => some 0

def compileAndTWeaken (f : Formula) (w : StratificationWitness) (scope : Nat) : Comb :=
  let c := translateFormula f
  let distMap := buildDynamicDistanceMap w scope
  algorithmicTWeaking c distMap

end UntypedComb
