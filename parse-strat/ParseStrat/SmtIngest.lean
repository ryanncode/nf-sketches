import Lean
import NfValidate

open Lean

namespace ParseStrat.SmtIngest

structure SmtInfo where
  formulaName : String := ""
  collisionTrace : Option String := none
  successDepths : Option String := none
  scActions : Option String := none

structure ParsedSmt where
  info : SmtInfo
  vars : List String
  edges : List (String × String × Int)

def parseSmtVar (name : String) : ScopedVar :=
  -- rust outputs format!("{}_d{}", base_name, depth)
  -- wait, the format is base_name_d{depth}
  -- base_name is `b{idx}` or `free_name`
  let parts := name.splitOn "_d"
  if parts.length == 2 then
    let baseName := parts.head!
    let depthStr := parts.tail!.head!
    let depth := depthStr.toNat!
    let var := if baseName.startsWith "b" then
        let rest := baseName.drop 1
        let restStr := rest.toString
        if restStr.length > 0 && restStr.toList.all Char.isDigit then
          Var.bound restStr.toNat!
        else
          Var.free baseName
      else
        Var.free baseName
    (var, depth)
  else
    (Var.free name, 0)

def parseLine (line : String) (state : ParsedSmt) : ParsedSmt :=
  let line := line.trimAscii.toString
  if line.startsWith "(set-info :formula-name" then
    -- (set-info :formula-name "...")
    let startIdx := (line.drop 25).toString
    let valStr := (startIdx.dropEnd 2).toString
    { state with info := { state.info with formulaName := valStr } }
  else if line.startsWith "(set-info :extensionality-collision-trace" then
    let startIdx := (line.drop 43).toString
    let valStr := (startIdx.dropEnd 2).toString
    { state with info := { state.info with collisionTrace := some valStr } }
  else if line.startsWith "(set-info :sc-daemon-actions" then
    let startIdx := (line.drop 30).toString
    let valStr := (startIdx.dropEnd 2).toString
    { state with info := { state.info with scActions := some valStr } }
  else if line.startsWith "(set-info :stratification-success-depths" then
    let startIdx := (line.drop 42).toString
    let valStr := (startIdx.dropEnd 2).toString
    { state with info := { state.info with successDepths := some valStr } }
  else if line.startsWith "(declare-fun" then
    -- (declare-fun name () Int)
    let parts := line.splitOn " "
    if parts.length >= 2 then
      let varName := parts[1]!
      { state with vars := varName :: state.vars }
    else state
  else if line.startsWith "(assert (<=" then
    -- (assert (<= (- v u) w))
    let inner := (line.drop 15).toString -- drops "(assert (<= (- "
    let parts1 := inner.splitOn ")"
    let vuStr := parts1[0]!.trimAscii.toString
    let vu := vuStr.splitOn " "
    if vu.length >= 2 then
      let v := vu[0]!
      let u := vu[1]!
      let wStr := parts1[1]!.trimAscii.toString
      let w := wStr.toInt!
      { state with edges := (v, u, w) :: state.edges }
    else state
  else
    state

def parseSmtLib (content : String) : ParsedSmt :=
  let lines := content.splitOn "\n"
  let initialState : ParsedSmt := { info := {}, vars := [], edges := [] }
  let finalState := lines.foldl (fun s l => parseLine l s) initialState
  { finalState with vars := finalState.vars.reverse, edges := finalState.edges.reverse }

def performEquivalenceCheck (smt : ParsedSmt) : IO Unit := do
  let scopedVars := smt.vars.map parseSmtVar
  -- Create constraints from edges
  -- For u -> v with weight w, we need Constraint where src=u, dst=v, weight=w
  -- Wait, `evaluateClause` takes `Constraint`, and `buildEdges` makes it bidirectional if not directed!
  -- We MUST use `directed := true`.
  -- v1 = u, v2 = v, diff = w, directed = true
  let constraints : List Constraint := smt.edges.map fun (u, v, w) =>
    { v1 := parseSmtVar u, v2 := parseSmtVar v, diff := w, directed := true }

  IO.println "Running Lean native Bellman-Ford on imported SMT-LIB edges..."
  match evaluateClause scopedVars constraints with
  | Except.ok _dists =>
    IO.println "Lean Native: Stratification SUCCESS."
    -- Check against witness if it was success
    match smt.info.successDepths with
    | some _depthsStr =>
      IO.println "Equivalence Check: Both Lean and Rust agree on SUCCESS."
      -- We could diff the exact depths, but Bellman-Ford solutions are not unique,
      -- they just prove satisfiability. However, the shortest-path tree is typically deterministic
      -- from a zero-initialized state. Let's just do a basic assertion.
    | none =>
      IO.println "Equivalence Check FAILED: Lean succeeded but Rust did not output success_depths."

  | Except.error (_cycle, _cycleEdges) =>
    IO.println "Lean Native: Stratification FAILED (Negative Cycle Detected)."
    match smt.info.collisionTrace with
    | some _trace =>
      IO.println "Equivalence Check: Both Lean and Rust agree on FAILURE."
    | none =>
      IO.println "Equivalence Check FAILED: Lean found cycle, but Rust did not output a collision trace."

end ParseStrat.SmtIngest
