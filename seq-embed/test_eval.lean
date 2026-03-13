import NfValidate
import SeqEmbed.Basic

def mkIff (p q : Formula) : Formula :=
  Formula.conj (Formula.impl p q) (Formula.impl q p)

def phi1 := Formula.eq (Var.bound 0) (Var.free "A")
def eval1 := mkIff (Formula.mem (Var.bound 0) (Var.free "A")) phi1

def phi2 := Formula.neg (Formula.mem (Var.bound 0) (Var.free "S"))
def eval2 := mkIff (Formula.mem (Var.bound 0) (Var.free "S")) phi2

def phi3 := Formula.conj (Formula.mem (Var.bound 0) (Var.free "B")) (Formula.mem (Var.free "B") (Var.free "C"))
def eval3 := mkIff (Formula.mem (Var.bound 0) (Var.free "C")) phi3

#eval evaluateFullFormula eval1
#eval evaluateFullFormula eval2
#eval evaluateFullFormula eval3
