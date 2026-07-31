import NfValidate

namespace NfValidate.SCCTests

def testVars : List ScopedVar := [ (Var.free "a", 0), (Var.free "b", 0), (Var.free "c", 0) ]

def testEdgesDAG : List Edge := [
  { src := (Var.free "a", 0), dst := (Var.free "b", 0), weight := 0 },
  { src := (Var.free "b", 0), dst := (Var.free "c", 0), weight := 0 }
]

def testEdgesCycle : List Edge := [
  { src := (Var.free "a", 0), dst := (Var.free "b", 0), weight := 0 },
  { src := (Var.free "b", 0), dst := (Var.free "c", 0), weight := 0 },
  { src := (Var.free "c", 0), dst := (Var.free "a", 0), weight := 0 }
]

def testSCCFlatteningDAG : Bool :=
  let sccs := kosarajuSCC testVars testEdgesDAG
  sccs.length == 3

def testSCCFlatteningCycle : Bool :=
  let sccs := kosarajuSCC testVars testEdgesCycle
  sccs.length == 1

#eval testSCCFlatteningDAG
#eval testSCCFlatteningCycle

end NfValidate.SCCTests
