import NfValidate.GraphSemantics
import NfValidate.BellmanFordInvariants

def v1 : Var := "v1"
def v2 : Var := "v2"
def v3 : Var := "v3"

def edges : List Edge := [
  { src := v1, dst := v2, weight := 5 },
  { src := v2, dst := v3, weight := -2 }
]

def initial_dist : List (Var × Int) := [(v1, 0), (v2, 100), (v3, 100)]
def initial_pred : List (Var × Var) := []

def step1 := relaxEdges edges initial_dist initial_pred
def step2 := relaxEdges edges step1.1 step1.2.1

#eval step1.1
#eval step1.2.2

#eval step2.1
#eval step2.2

