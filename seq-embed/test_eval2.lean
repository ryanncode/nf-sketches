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

def eval2_alt := mkIff (Formula.mem (Var.bound 0) (Var.free "S")) (Formula.neg (Formula.mem (Var.bound 0) (Var.bound 0)))

#eval evaluateStratification eval1
#eval evaluateStratification eval2
#eval evaluateStratification eval3
#eval evaluateStratification eval2_alt
