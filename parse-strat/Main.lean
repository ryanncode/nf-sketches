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
  | iff : Token
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
    | '<' :: '-' :: '>' :: rest => go rest (Token.iff :: acc)
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


def expandMacro (f : Formula) (params : List String) (args : List String) : Formula :=
  let rec goVar (v : Var) : Var :=
    match v with
    | Var.free s =>
      match params.zip args |>.find? (fun (k, _) => k == s) with
      | some (_, v') => Var.free v'
      | none => v
    | _ => v
  let goAtomic (a : Atomic) : Atomic :=
    match a with
    | Atomic.eq x y => Atomic.eq (goVar x) (goVar y)
    | Atomic.mem x y => Atomic.mem (goVar x) (goVar y)
    | _ => a
  let rec go (f : Formula) : Formula :=
    match f with
    | Formula.atom a => Formula.atom (goAtomic a)
    | Formula.neg p => Formula.neg (go p)
    | Formula.conj p q => Formula.conj (go p) (go q)
    | Formula.disj p q => Formula.disj (go p) (go q)
    | Formula.impl p q => Formula.impl (go p) (go q)
    | Formula.univ n x p => Formula.univ n x (go p)
    | Formula.comp n x p => Formula.comp n x (go p)
  go f

partial def parseArgs (toks : List Token) (acc : List String) : Option (List String × List Token) :=
  match toks with
  | Token.rparen :: rest => some (acc.reverse, rest)
  | Token.var x :: Token.rparen :: rest => some ((x :: acc).reverse, rest)
  | Token.var x :: Token.comma :: rest => parseArgs rest (x :: acc)
  | _ => none

partial def parseAtomic (toks : List Token) (macros : List (String × List String × Formula)) : Option (Formula × List Token) :=
  match toks with
  | Token.var x :: Token.eq :: Token.var y :: rest => some (Formula.atom (Atomic.eq (Var.free x) (Var.free y)), rest)
  | Token.var x :: Token.mem :: Token.var y :: rest => some (Formula.atom (Atomic.mem (Var.free x) (Var.free y)), rest)
  | Token.var f :: Token.lparen :: rest =>
      match parseArgs rest [] with
      | some (args, rest') =>
          match macros.find? (fun (k, _, _) => k == f) with
          | some (_, params, formula) =>
              if params.length == args.length then
                some (expandMacro formula params args, rest')
              else none
          | none => none
      | none => none
  | Token.var x :: rest => some (Formula.atom (Atomic.eq (Var.free x) (Var.free x)), rest) -- fallback for propositions
  | _ => none

mutual
partial def parsePrimary (toks : List Token) (macros : List (String × List String × Formula)) : Option (Formula × List Token) :=
  match toks with
  | Token.neg :: rest =>
      match parsePrimary rest macros with
      | some (f, rest') => some (Formula.neg f, rest')
      | none => none
  | Token.forall_tok :: Token.var x :: Token.comma :: rest =>
      match parseIff rest macros with
      | some (f, rest') => some (Formula.univ 0 x f, rest')
      | none => none
  | Token.exists_tok :: Token.var x :: Token.comma :: rest =>
      -- Emulated via ~forall x, ~P
      match parseIff rest macros with
      | some (f, rest') => some (Formula.neg (Formula.univ 0 x (Formula.neg f)), rest')
      | none => none
  | Token.lparen :: rest =>
      match parseIff rest macros with
      | some (f, Token.rparen :: rest') => some (f, rest')
      | _ => none
  | _ => parseAtomic toks macros

partial def parseConj (toks : List Token) (macros : List (String × List String × Formula)) : Option (Formula × List Token) :=
  match parsePrimary toks macros with
  | some (f1, Token.conj :: rest) =>
      match parseConj rest macros with
      | some (f2, rest') => some (Formula.conj f1 f2, rest')
      | none => none
  | res => res

partial def parseDisj (toks : List Token) (macros : List (String × List String × Formula)) : Option (Formula × List Token) :=
  match parseConj toks macros with
  | some (f1, Token.disj :: rest) =>
      match parseDisj rest macros with
      | some (f2, rest') => some (Formula.disj f1 f2, rest')
      | none => none
  | res => res

partial def parseImpl (toks : List Token) (macros : List (String × List String × Formula)) : Option (Formula × List Token) :=
  match parseDisj toks macros with
  | some (f1, Token.impl :: rest) =>
      match parseImpl rest macros with
      | some (f2, rest') => some (Formula.impl f1 f2, rest')
      | none => none
  | res => res

partial def parseIff (toks : List Token) (macros : List (String × List String × Formula)) : Option (Formula × List Token) :=
  match parseImpl toks macros with
  | some (f1, Token.iff :: rest) =>
      match parseIff rest macros with
      | some (f2, rest') => some (Formula.conj (Formula.impl f1 f2) (Formula.impl f2 f1), rest')
      | none => none
  | res => res
end

partial def parseFormula (s : String) (macros : List (String × List String × Formula)) : Option Formula :=
  match parseIff (tokenize s) macros with
  | some (f, []) => some f
  | _ => none

--------------------------------------------------------------------------------
-- COMMAND LOOP
--------------------------------------------------------------------------------

structure GlobalEnv where
  theorems : List (String × Formula)
  macros : List (String × List String × Formula) := []
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
    match parseFormula formulaStr env.macros with
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
    match parseFormula formulaStr env.macros with
    | some f =>
      match evaluateFullFormula f with
      | StratificationResult.success _ => stdout.putStrLn "Stratification successful. Topologically sound."
      | StratificationResult.failure _ _ => stdout.putStrLn "Error: Negative-weight cycle detected"
      repl stdin stdout env ps
    | none =>
      stdout.putStrLn "Failed to parse formula."
      repl stdin stdout env ps
  else if cmd == "step" then
    let formulaStr := String.intercalate " " args
    match parseFormula formulaStr env.macros with
    | some f =>
      let constraints := extractConstraints f
      stdout.putStrLn "--- Extracting Constraints ---"
      for c in constraints do
        stdout.putStrLn (reprStr c)

      let edges := buildEdges constraints
      let vars := getVars constraints

      stdout.putStrLn "--- Graph Nodes ---"
      for v in vars do
        stdout.putStrLn (reprStr v)

      stdout.putStrLn "--- Graph Edges ---"
      for e in edges do
        stdout.putStrLn (reprStr e)

      stdout.putStrLn "--- Running Bellman-Ford ---"
      match evaluateFullFormula f with
      | StratificationResult.success _ => stdout.putStrLn "Stratification successful."
      | StratificationResult.failure _ _ => stdout.putStrLn "Error: Negative-weight cycle detected"
      repl stdin stdout env ps
    | none =>
      stdout.putStrLn "Failed to parse formula."
      repl stdin stdout env ps
  else if cmd == "show_goal" then
    if ps.isSome then stdout.putStrLn (printState ps.get!) else stdout.putStrLn "No active goals."
    repl stdin stdout env ps
  else match ps with
  | none =>
    if cmd == "theorem" then
      let name := args.head!
      let formulaStr := String.intercalate " " args.tail
      match parseFormula formulaStr env.macros with
      | some f =>
        stdout.putStrLn s!"Starting proof of {name}"
        let initialGoal : Goal := { ctx := env.theorems, target := f }
        repl stdin stdout env (some [initialGoal])
      | none =>
        stdout.putStrLn "Failed to parse formula."
        repl stdin stdout env ps
    else if cmd == "deff" then
      -- Syntax: deff name arg1 arg2 ... := formula
      let eqIdx := args.findIdx? (fun x => x == ":=")
      match eqIdx with
      | some i =>
        let macroArgs := args.take i
        if macroArgs.isEmpty then
          stdout.putStrLn "Usage: deff <name> [args...] := <formula>"
          repl stdin stdout env ps
        else
          let macroName := macroArgs.head!
          let macroParams := macroArgs.tail
          let formulaStr := String.intercalate " " (args.drop (i + 1))
          match parseFormula formulaStr env.macros with
          | some f =>
            match evaluateFullFormula f with
            | StratificationResult.success _ =>
              stdout.putStrLn s!"Macro {macroName} defined and SCC flattened."
              repl stdin stdout { env with macros := (macroName, macroParams, f) :: env.macros } ps
            | StratificationResult.failure _ _ =>
              stdout.putStrLn "Failed to stratify macro. Negative cycle detected."
              repl stdin stdout env ps
          | none =>
            stdout.putStrLn "Failed to parse formula."
            repl stdin stdout env ps
      | none =>
        stdout.putStrLn "Usage: deff <name> [args...] := <formula>"
        repl stdin stdout env ps
    else if cmd == "assume" then
      let name := args.head!
      let formulaStr := String.intercalate " " args.tail
      match parseFormula formulaStr env.macros with
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
      match parseFormula formulaStr env.macros with
      | some f =>
        match evaluateFullFormula f with
        | StratificationResult.failure c e =>
          stdout.putStrLn "Extensionality Collision!"
          stdout.putStrLn (formatDetailedCycleSandbox c e)
          repl stdin stdout env (some state)
        | StratificationResult.success _ =>
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
