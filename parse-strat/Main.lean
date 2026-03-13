import NfValidate
import ParseStrat

def buildConjunction (atoms : List Formula) : Option Formula :=
  match atoms with
  | [] => none
  | [x] => some x
  | x :: xs =>
      match buildConjunction xs with
      | some rest => some (Formula.conj x rest)
      | none => none

--------------------------------------------------------------------------------
-- 7. COMPREHENSIVE PARSER FOR FIRST-ORDER LOGIC
--------------------------------------------------------------------------------
-- Converts raw user input strings into the Formula AST. Supports parentheses
-- and operator precedence (~, &, v, ->).

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
    | c :: rest =>
        if c.isAlphanum then
          let (varChars, rest') := cs.span Char.isAlphanum
          go rest' (Token.var (String.ofList varChars) :: acc)
        else
          go rest acc
  go s.toList []

partial def parseAtomic (toks : List Token) : Option (Formula × List Token) :=
  match toks with
  | Token.var x :: Token.eq :: Token.var y :: rest => some (Formula.atom (Atomic.eq (Var.free x) (Var.free y)), rest)
  | Token.var x :: Token.mem :: Token.var y :: rest => some (Formula.atom (Atomic.mem (Var.free x) (Var.free y)), rest)
  | Token.lparen :: _ =>
      -- forward declaration workaround: call parseImpl
      none -- replaced below
  | _ => none

mutual
partial def parsePrimary (toks : List Token) : Option (Formula × List Token) :=
  match toks with
  | Token.neg :: rest =>
      match parsePrimary rest with
      | some (f, rest') => some (Formula.neg f, rest')
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

partial def readFormulas (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) (acc : List Formula) : IO (List Formula) := do
  stdout.putStr "> "
  stdout.flush
  let line ← stdin.getLine
  let input := line.trimAscii.toString
  if input == "done" then
    return acc
  else
    match parseFormula input with
    | some f => readFormulas stdin stdout (acc ++ [f])
    | none =>
        stdout.putStrLn "Invalid format. Logical operators (~, &, v, ->) must be applied to full relations. Example: '~(x = y)', '(a e b) & (c = d)'."
        readFormulas stdin stdout acc

--------------------------------------------------------------------------------
-- 8. OUTPUT FORMATTING & SEMANTIC TRACE
--------------------------------------------------------------------------------
-- Translates the internal numerical evaluation results back into algebraic
-- proofs or type contradiction paths for the user.
--------------------------------------------------------------------------------
-- 9. MAIN EXECUTION LOOP
--------------------------------------------------------------------------------

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "=== NF Stratification Validator ==="
  stdout.putStrLn "Enter formulas to build a conjunction."
  stdout.putStrLn "Accepted syntax: Relational statements ('x = y', 'x e y') combined with logical operators ('~', '&', 'v', '->'). Example: '~(x = y) & (y e z)'."
  stdout.putStrLn "Type 'done' to evaluate the combined formula."

  let atoms ← readFormulas stdin stdout []
  match buildConjunction atoms with
  | none => stdout.putStrLn "Execution terminated. No formulas were entered."
  | some f =>
      stdout.putStrLn "\nEvaluating constraint graph with DNF conversion and cycle detection..."
      match evaluateFullFormula f with
      | StratificationResult.success witness =>
          stdout.putStrLn "Result: The formula is stratifiable."
          stdout.putStrLn s!"Witness Context: {formatWitness witness}"
      | StratificationResult.failure cycle edges =>
          stdout.putStrLn "Result: Not stratifiable. A type contradiction was detected in all branches."
          stdout.putStrLn (formatDetailedCycleSandbox cycle edges)
