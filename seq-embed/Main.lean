import NfValidate

--------------------------------------------------------------------------------
-- 1. SEQUENT DEFINITION & SYNTACTIC SUGAR
--------------------------------------------------------------------------------

abbrev Context := List Formula

structure Sequent where
  gamma : Context -- Antecedents (Left)
  delta : Context -- Succedents (Right)
  deriving Repr, BEq

-- To model comprehension, we need existential quantification and biconditionals.
-- We construct these from the primitive AST operators.
def mkIff (p q : Formula) : Formula :=
  Formula.conj (Formula.impl p q) (Formula.impl q p)

def mkExists (x : Var) (p : Formula) : Formula :=
  Formula.neg (Formula.univ x (Formula.neg p))

-- Constructs the NF Comprehension Axiom body: ∃x ∀y (y ∈ x ↔ φ)
def mkComprehensionAxiom (x y : Var) (phi : Formula) : Formula :=
  mkExists x (Formula.univ y (mkIff (Formula.mem y x) phi))

--------------------------------------------------------------------------------
-- 2. STRATIFIED SEQUENT CALCULUS
--------------------------------------------------------------------------------

-- Derivations are modeled as an inductive family indexed by Sequents.
-- This establishes the "deep embedding" required to isolate the deductive system.
inductive Derivation : Sequent → Type
  -- Identity
  | ax {Γ Δ : Context} (A : Formula) (hL : A ∈ Γ) (hR : A ∈ Δ) : Derivation ⟨Γ, Δ⟩

  -- Structural Rules (Weakening & Contraction)
  | weakenL {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, Δ⟩ → Derivation ⟨A :: Γ, Δ⟩
  | weakenR {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, Δ⟩ → Derivation ⟨Γ, A :: Δ⟩

  | contractL {Γ Δ : Context} (A : Formula) :
      Derivation ⟨A :: A :: Γ, Δ⟩ → Derivation ⟨A :: Γ, Δ⟩
  | contractR {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, A :: A :: Δ⟩ → Derivation ⟨Γ, A :: Δ⟩

  -- The Cut Rule
  -- Central to Aim 1: Tracking logical detours and proof normalization breakdowns.
  | cut {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, A :: Δ⟩ → Derivation ⟨A :: Γ, Δ⟩ → Derivation ⟨Γ, Δ⟩

  -- Basic Logical Rules (Conjunction used as a sample)
  | conjL {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨A :: B :: Γ, Δ⟩ → Derivation ⟨Formula.conj A B :: Γ, Δ⟩
  | conjR {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨Γ, A :: Δ⟩ → Derivation ⟨Γ, B :: Δ⟩ → Derivation ⟨Γ, Formula.conj A B :: Δ⟩

  ------------------------------------------------------------------------------
  -- 3. RESTRICTED COMPREHENSION RULE
  ------------------------------------------------------------------------------
  -- This is the strict bridge to the Bellman-Ford algorithmic validator.
  -- The derivation step requires a proof that evaluating the formula's stratification
  -- results in a successful numerical witness.
  | compL {Γ Δ : Context} (x y : Var) (phi : Formula) (witness : List (Var × Int))
      (h_strat : evaluateStratification phi = StratificationResult.success witness) :
      Derivation ⟨mkComprehensionAxiom x y phi :: Γ, Δ⟩

--------------------------------------------------------------------------------
-- 4. BASIC INPUT/OUTPUT EXECUTABLE
--------------------------------------------------------------------------------
-- Evaluates raw input against the computational restrictions of the calculus.

partial def loop (stdin : IO.FS.Stream) (stdout : IO.FS.Stream) : IO Unit := do
  stdout.putStr "> "
  stdout.flush
  let line ← stdin.getLine
  let input := line.trimAscii.toString

  if input == "quit" then
    pure ()
  else if input == "" then
    loop stdin stdout
  else
    match parseFormula input with
    | some phi =>
        stdout.putStrLn "AST parsed successfully."
        match evaluateStratification phi with
        | StratificationResult.success _ =>
            stdout.putStrLn "Result: Stratification verified."
            stdout.putStrLn "Status: ELIGIBLE for compL derivation step."
        | StratificationResult.failure _ _ =>
            stdout.putStrLn "Result: Type-level contradiction detected."
            stdout.putStrLn "Status: REJECTED by compL (compilation failure)."
    | none =>
        stdout.putStrLn "Invalid format. Please check your syntax."
    loop stdin stdout

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "=== Stratified Sequent Calculus Environment ==="
  stdout.putStrLn "Enter a formula to test its eligibility for the Comprehension Axiom (compL)."
  stdout.putStrLn "Type 'quit' to exit."

  loop stdin stdout
