import NfValidate
import SeqEmbed.Basic

def phi1 : Formula := Formula.eq (Var.bound 0) (Var.free "z")
#eval checkStrat phi1
