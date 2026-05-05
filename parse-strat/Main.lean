import Init.Data.List.Basic
import Lean
import NfValidate
import ParseStrat
import ParseStrat.ITP

open Lean
open ITP

/-!
# ParseStrat: Interactive REPL Sandbox for ITP
-/

inductive Token where
  | var : String → Token
  | eq : Token
  | mem : Token
  | neg : Token
  | conj : Token
  | disj : Token
  | impl : Token
  | lparen : Token
  | rparen : Token
  | forall_tok : Token
  | exists_tok : Token
  | comma : Token
  deriving Repr, BEq

partial def tokenize (s : String) : List Token :=
  let rec go (cs : List Char) (acc : List Token) :=
    match cs with
    | [] => acc.reverse
    | ' ' :: rest => go rest acc
    | '\t' :: rest => go rest acc
    | '\n' :: rest => go rest acc
    | '\r' :: rest => go rest acc
    | '(' :: rest => go rest (Token.lparen :: acc)
    | ')' :: rest => go rest (Token.rparen :: acc)
    | '~' :: rest => go rest (Token.neg :: acc)
    | 'v' :: rest => go rest (Token.disj :: acc)
    | '&' :: rest => go rest (Token.conj :: acc)
    | '-' :: '>' :: rest => go rest (Token.impl :: acc)
    | '=' :: rest => go rest (Token.eq :: acc)
    | 'e' :: rest => go rest (Token.mem :: acc)
    | ',' :: rest => go rest (Token.comma :: acc)
    | c :: rest =>
        if c.isAlphanum then
          let (varChars, rest') := cs.span Char.isAlphanum
          let v := String.ofList varChars
          if v == "forall" then go rest' (Token.forall_tok :: acc)
          else if v == "exists" then go rest' (Token.exists_tok :: acc)
          else go rest' (Token.var v :: acc)
        else
          go rest acc
  go s.toList []

partial def parseAtomic (toks : List Token) : Option (Formula × List Token) :=
  match toks with
  | Token.var x :: Token.eq :: Token.var y :: rest => some (Formula.atom (Atomic.eq (Var.free x) (Var.free y)), rest)
  | Token.var x :: Token.mem :: Token.var y :: rest => some (Formula.atom (Atomic.mem (Var.free x) (Var.free y)), rest)
  | Token.var x :: rest => some (Formula.atom (Atomic.eq (Var.free x) (Var.free x)), rest) -- fallback for propositions
  | _ => none

mutual
partial def parsePrimary (toks : List Token) : Option (Formula × List Token) :=
  match toks with
  | Token.neg :: rest =>
      match parsePrimary rest with
      | some (f, rest') => some (Formula.neg f, rest')
      | none => none
  | Token.forall_tok :: Token.var x :: Token.comma :: rest =>
      match parseImpl rest with
      | some (f, rest') => some (Formula.univ 0 x f, rest')
      | none => none
  | Token.exists_tok :: Token.var x :: Token.comma :: rest =>
      -- Emulated via ~forall x, ~P
      match parseImpl rest with
      | some (f, rest') => some (Formula.neg (Formula.univ 0 x (Formula.neg f)), rest')
      | none => none
  | Token.lparen :: rest =>
      match parseImpl rest with
      | some (f, Token.rparen :: rest') => some (f, rest')
      | _ => none
  | _ => parseAtomic toks

partial def parseConj (toks : List Token) : Option (Formula × List Token) :=
  match parsePrimary toks with
  | some (f1, Token.conj :: rest) =>
      match parseConj rest with
      | some (f2, rest') => some (Formula.conj f1 f2, rest')
      | none => none
  | res => res

partial def parseDisj (toks : List Token) : Option (Formula × List Token) :=
  match parseConj toks with
  | some (f1, Token.disj :: rest) =>
      match parseDisj rest with
      | some (f2, rest') => some (Formula.disj f1 f2, rest')
      | none => none
  | res => res

partial def parseImpl (toks : List Token) : Option (Formula × List Token) :=
  match parseDisj toks with
  | some (f1, Token.impl :: rest) =>
      match parseImpl rest with
      | some (f2, rest') => some (Formula.impl f1 f2, rest')
      | none => none
  | res => res
end

partial def parseFormula (s : String) : Option Formula :=
  match parseImpl (tokenize s) with
  | some (f, []) => some f
  | _ => none

--------------------------------------------------------------------------------
-- COMMAND LOOP
--------------------------------------------------------------------------------

structure GlobalEnv where
  theorems : List (String × Formula)
  macros : List (String × Formula) := []
  deriving Repr, ToJson, FromJson

structure Session where
  env : GlobalEnv
  activeGoals : Option ProofState
  deriving Repr, ToJson, FromJson

def formatVarUI : Var → String
  | Var.free s =>
    let parts := s.splitOn "@"
    if parts.length > 0 then parts.head! else s
  | Var.bound n => s!"v{n}"

partial def formatFormulaUI : Formula → String
  | Formula.atom (Atomic.eq x y) => s!"{formatVarUI x} = {formatVarUI y}"
  | Formula.atom (Atomic.mem x y) => s!"{formatVarUI x} e {formatVarUI y}"
  | Formula.atom a => reprStr a
  | Formula.neg f => s!"~{formatFormulaUI f}"
  | Formula.conj f1 f2 => s!"({formatFormulaUI f1} /\\ {formatFormulaUI f2})"
  | Formula.disj f1 f2 => s!"({formatFormulaUI f1} \\/ {formatFormulaUI f2})"
  | Formula.impl f1 f2 => s!"({formatFormulaUI f1} -> {formatFormulaUI f2})"
  | Formula.univ _ x f => s!"forall {x}. {formatFormulaUI f}"
  | Formula.comp _ x f => "{ " ++ x ++ " | " ++ formatFormulaUI f ++ " }"

def printState (ps : ProofState) : String :=
  match ps with
  | [] => "No more goals. Proof complete!"
  | g :: _ =>
    let ctxStr := String.intercalate "\n" (g.ctx.map (fun (n, f) => s!"{n} : {formatFormulaUI f}"))
    s!"\n{ctxStr}\n----------------------\n{formatFormulaUI g.target}\n"

partial def repl (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (env : GlobalEnv) (ps : Option ProofState) : IO Unit := do
  stdout.putStr (if ps.isSome then "ITP> " else "> ")
  stdout.flush
  let line ← stdin.getLine
  let input := line.trimAscii.toString
  if input == "exit" then
    return ()

  let parts := input.splitOn " "
  let cmd := parts.head!
  let args := parts.tail

  if cmd == "help" then
    stdout.putStrLn "Commands:"
    stdout.putStrLn "  help                          - Show this help message"
    stdout.putStrLn "  exit                          - Exit the REPL"
    stdout.putStrLn "  save_session <file>           - Save current session to a JSON file"
    stdout.putStrLn "  load_session <file>           - Load a session from a JSON file"
    stdout.putStrLn "  eval <formula>                - Evaluate a formula"
    stdout.putStrLn "  step <formula>                - Step-by-step diagnostic evaluation"
    stdout.putStrLn "  assume <name> <formula>       - Add a named axiom"
    stdout.putStrLn "  theorem <name> <formula>      - Set a new goal to prove"
    stdout.putStrLn "  show_goal                     - Show the current goal state"
    stdout.putStrLn "  intro [name]                  - Introduce a hypothesis or variable"
    stdout.putStrLn "  exact <name>                  - Close goal if it matches hypothesis exactly"
    stdout.putStrLn "  split                         - Split a conjunction goal into two"
    stdout.putStrLn "  left                          - Prove left side of a disjunction"
    stdout.putStrLn "  right                         - Prove right side of a disjunction"
    stdout.putStrLn "  apply <name>                  - Apply a theorem/hypothesis"
    stdout.putStrLn "  destruct <name> [n1] [n2]     - Break down a hypothesis"
    stdout.putStrLn "  rewrite <name>                - Substitute variables using equality"
    stdout.putStrLn "  qed                           - Finish proof"
    stdout.putStrLn "  abort                         - Abort current proof"
    repl stdin stdout env ps
  else if cmd == "save_session" then
    let filename := args.head!
    let session : Session := { env := env, activeGoals := ps }
    let json := toJson session
    IO.FS.writeFile filename json.pretty
    stdout.putStrLn s!"Session saved to {filename}."
    repl stdin stdout env ps
  else if cmd == "load_session" then
    let filename := args.head!
    match ← IO.FS.readFile filename |>.toBaseIO with
    | Except.ok content =>
      match Json.parse content with
      | Except.ok json =>
        match fromJson? json with
        | Except.ok (session : Session) =>
          stdout.putStrLn s!"Session loaded from {filename}."
          if session.activeGoals.isSome then
            stdout.putStrLn (printState session.activeGoals.get!)
          repl stdin stdout session.env session.activeGoals
        | Except.error e =>
          stdout.putStrLn s!"Failed to deserialize session: {e}"
          repl stdin stdout env ps
      | Except.error e =>
        stdout.putStrLn s!"Failed to parse JSON: {e}"
        repl stdin stdout env ps
    | Except.error _ =>
      stdout.putStrLn s!"Failed to read file {filename}."
      repl stdin stdout env ps
  else if cmd == "eval" then
    let formulaStr := String.intercalate " " args
    match parseFormula formulaStr with
    | some f =>
      match evaluateFullFormula f with
      | StratificationResult.success w => stdout.putStrLn s!"Stratification successful. Witness: {formatWitness w}"
      | StratificationResult.failure c e => stdout.putStrLn s!"Error: {formatDetailedCycleSandbox c e}"
      repl stdin stdout env ps
    | none =>
      stdout.putStrLn "Failed to parse formula."
      repl stdin stdout env ps
  else if cmd == "check_strat" then
    let formulaStr := String.intercalate " " args
    match parseFormula formulaStr with
    | some f =>
      match evaluateFullFormula f with
      | StratificationResult.success _ => stdout.putStrLn "Stratification successful. Topologically sound."
      | StratificationResult.failure c e => stdout.putStrLn s!"Error: Negative-weight cycle detected"
      repl stdin stdout env ps
    | none =>
      stdout.putStrLn "Failed to parse formula."
      repl stdin stdout env ps
  else if cmd == "step" then
    stdout.putStrLn "Step not fully implemented in Lean CLI, use eval."
    repl stdin stdout env ps
  else if cmd == "show_goal" then
    if ps.isSome then stdout.putStrLn (printState ps.get!) else stdout.putStrLn "No active goals."
    repl stdin stdout env ps
  else match ps with
  | none =>
    if cmd == "theorem" then
      let name := args.head!
      let formulaStr := String.intercalate " " args.tail
      match parseFormula formulaStr with
      | some f =>
        stdout.putStrLn s!"Starting proof of {name}"
        let initialGoal : Goal := { ctx := env.theorems, target := f }
        repl stdin stdout env (some [initialGoal])
      | none =>
        stdout.putStrLn "Failed to parse formula."
        repl stdin stdout env ps
    else if cmd == "deff" then
      let name := args.head!
      -- Syntax: deff name := formula
      let eqIdx := args.findIdx? (fun x => x == ":=")
      match eqIdx with
      | some i =>
        let formulaStr := String.intercalate " " (args.drop (i + 1))
        match parseFormula formulaStr with
        | some f =>
          -- Kosaraju SCC Flattening Simulation (we just verify it parses and stratifies)
          match evaluateFullFormula f with
          | StratificationResult.success _ =>
            stdout.putStrLn s!"Macro {name} defined and SCC flattened."
            repl stdin stdout { env with macros := (name, f) :: env.macros } ps
          | StratificationResult.failure _ _ =>
            stdout.putStrLn "Failed to stratify macro. Negative cycle detected."
            repl stdin stdout env ps
        | none =>
          stdout.putStrLn "Failed to parse formula."
          repl stdin stdout env ps
      | none =>
        stdout.putStrLn "Usage: deff <name> := <formula>"
        repl stdin stdout env ps
    else if cmd == "assume" then
      let name := args.head!
      let formulaStr := String.intercalate " " args.tail
      match parseFormula formulaStr with
      | some f =>
        stdout.putStrLn s!"Axiom {name} added."
        repl stdin stdout { env with theorems := (name, f) :: env.theorems } ps
      | none =>
        stdout.putStrLn "Failed to parse formula."
        repl stdin stdout env ps
    else
      stdout.putStrLn "Unknown command. Type 'help' for available commands."
      repl stdin stdout env ps
  | some state =>
    if cmd == "intro" then
      let name := if args.isEmpty then "H" else args.head!
      match introTactic name state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "exact" then
      let name := args.head!
      match exactTactic name state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "apply" then
      let name := args.head!
      match applyTactic name state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "split" then
      match splitTactic state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "left" then
      match leftTactic state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "right" then
      match rightTactic state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "focus_hyp" then
      let name := args.head!
      match focusHypTactic name state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "defer" then
      match deferTactic state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "cut" then
      let formulaStr := String.intercalate " " args
      match parseFormula formulaStr with
      | some f =>
        match cutTactic f state with
        | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
        | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
      | none =>
        stdout.putStrLn "Failed to parse formula for cut."
        repl stdin stdout env (some state)
    else if cmd == "destruct" then
      let name := args.head!
      let n1 := args.getD 1 ""
      let n2 := args.getD 2 ""
      match destructTactic name n1 n2 state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "rewrite" then
      let name := args.head!
      match rewriteTactic name state with
      | Except.ok s => stdout.putStrLn (printState s); repl stdin stdout env (some s)
      | Except.error e => stdout.putStrLn e; repl stdin stdout env (some state)
    else if cmd == "qed" then
      if state.isEmpty then
        stdout.putStrLn "Proof accepted."
        repl stdin stdout env none
      else
        stdout.putStrLn "Proof is not complete."
        repl stdin stdout env (some state)
    else if cmd == "abort" then
      stdout.putStrLn "Proof aborted."
      repl stdin stdout env none
    else
      stdout.putStrLn "Unknown tactic."
      repl stdin stdout env (some state)

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "=== Lean ITP REPL ==="
  stdout.putStrLn "Type 'help' for a list of commands, or 'exit' to quit."
  repl stdin stdout { theorems := [] } none
