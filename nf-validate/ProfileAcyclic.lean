import NfValidate
import NfValidate.BowlerTranslation

open Bowler

-- Profiling the Bowler acyclic translation

def makeDeepFormula : Nat → Formula
  | 0 => Formula.mem (Var.free "a") (Var.free "b")
  | n + 1 =>
      let inner := makeDeepFormula n
      let v1 := Var.free s!"x_{n}"
      let v2 := Var.free s!"y_{n}"
      Formula.conj
        (Formula.conj (Formula.eq v1 v2) (Formula.eq v2 v1))
        inner

def sizeOfFormula : Formula → Nat
  | Formula.atom _ => 1
  | Formula.neg p => 1 + sizeOfFormula p
  | Formula.conj p q => 1 + sizeOfFormula p + sizeOfFormula q
  | Formula.disj p q => 1 + sizeOfFormula p + sizeOfFormula q
  | Formula.impl p q => 1 + sizeOfFormula p + sizeOfFormula q
  | Formula.univ _ _ p => 1 + sizeOfFormula p
  | Formula.comp _ _ p => 1 + sizeOfFormula p

def profileFormula (n : Nat) : IO Unit := do
  let f := makeDeepFormula n
  let sizeBefore := sizeOfFormula f
  let t1 ← IO.monoMsNow
  -- count cycles
  let constraints := extractConstraints f
  let edges := buildEdges constraints
  let zeroEdges := edges.filter (fun e => e.weight == 0)
  let vars := getVars constraints
  let sccs := findSCCs vars zeroEdges
  let cyclicSccs := sccs.filter (fun scc => scc.length > 1)

  let fFlat := flattenGraph f
  let t2 ← IO.monoMsNow
  let sizeAfter := sizeOfFormula fFlat
  IO.println s!"Depth: {n}"
  IO.println s!"  Cycles Found: {cyclicSccs.length}"
  IO.println s!"  Size Before: {sizeBefore}"
  IO.println s!"  Size After:  {sizeAfter}"
  IO.println s!"  Time (ms):   {t2 - t1}"

def main : IO Unit := do
  IO.println "Profiling Acyclic Translation (flattenGraph)..."
  for i in [1, 5, 10, 20, 50, 100] do
    profileFormula i
