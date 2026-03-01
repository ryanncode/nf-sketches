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
-- VARIABLE SUBSTITUTION & FRESH VARIABLES
--------------------------------------------------------------------------------

def freeVars : Formula → List Var
  | Formula.eq y z => [y, z]
  | Formula.mem y z => [y, z]
  | Formula.neg p => freeVars p
  | Formula.conj p q => freeVars p ++ freeVars q
  | Formula.disj p q => freeVars p ++ freeVars q
  | Formula.impl p q => freeVars p ++ freeVars q
  | Formula.univ y p => (freeVars p).filter (· != y)

partial def freshVar (avoid : List Var) (base : Var) : Var :=
  if avoid.contains base then
    freshVar avoid (base ++ "'")
  else
    base

def substVar (v : Var) (x : Var) (t : Var) : Var :=
  if v == x then t else v

partial def subst (x : Var) (t : Var) (f : Formula) : Formula :=
  match f with
  | Formula.eq y z => Formula.eq (substVar y x t) (substVar z x t)
  | Formula.mem y z => Formula.mem (substVar y x t) (substVar z x t)
  | Formula.neg p => Formula.neg (subst x t p)
  | Formula.conj p q => Formula.conj (subst x t p) (subst x t q)
  | Formula.disj p q => Formula.disj (subst x t p) (subst x t q)
  | Formula.impl p q => Formula.impl (subst x t p) (subst x t q)
  | Formula.univ y p =>
      if y == x then
        Formula.univ y p
      else if y == t then
        let fresh := freshVar (freeVars p ++ [x, t]) y
        let p' := subst y fresh p
        Formula.univ fresh (subst x t p')
      else
        Formula.univ y (subst x t p)

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

  -- Logical Rules: Conjunction
  | conjL {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨A :: B :: Γ, Δ⟩ → Derivation ⟨Formula.conj A B :: Γ, Δ⟩
  | conjR {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨Γ, A :: Δ⟩ → Derivation ⟨Γ, B :: Δ⟩ → Derivation ⟨Γ, Formula.conj A B :: Δ⟩

  -- Logical Rules: Disjunction
  | disjL {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨A :: Γ, Δ⟩ → Derivation ⟨B :: Γ, Δ⟩ → Derivation ⟨Formula.disj A B :: Γ, Δ⟩
  | disjR {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨Γ, A :: B :: Δ⟩ → Derivation ⟨Γ, Formula.disj A B :: Δ⟩

  -- Logical Rules: Implication
  | implL {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨Γ, A :: Δ⟩ → Derivation ⟨B :: Γ, Δ⟩ → Derivation ⟨Formula.impl A B :: Γ, Δ⟩
  | implR {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨A :: Γ, B :: Δ⟩ → Derivation ⟨Γ, Formula.impl A B :: Δ⟩

  -- Logical Rules: Negation
  | negL {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, A :: Δ⟩ → Derivation ⟨Formula.neg A :: Γ, Δ⟩
  | negR {Γ Δ : Context} (A : Formula) :
      Derivation ⟨A :: Γ, Δ⟩ → Derivation ⟨Γ, Formula.neg A :: Δ⟩

  -- Logical Rules: Universal Quantification
  | univL {Γ Δ : Context} (x : Var) (A : Formula) (t : Var) :
      Derivation ⟨subst x t A :: Γ, Δ⟩ → Derivation ⟨Formula.univ x A :: Γ, Δ⟩
  | univR {Γ Δ : Context} (x : Var) (A : Formula) (y : Var)
      (h_fresh_gamma : ∀ F ∈ Γ, y ∉ freeVars F)
      (h_fresh_delta : ∀ F ∈ Δ, y ∉ freeVars F) :
      Derivation ⟨Γ, subst x y A :: Δ⟩ → Derivation ⟨Γ, Formula.univ x A :: Δ⟩

  -- Logical Rules: Existential Quantification
  | existsL {Γ Δ : Context} (x : Var) (A : Formula) (y : Var)
      (h_fresh_gamma : ∀ F ∈ Γ, y ∉ freeVars F)
      (h_fresh_delta : ∀ F ∈ Δ, y ∉ freeVars F) :
      Derivation ⟨subst x y A :: Γ, Δ⟩ → Derivation ⟨mkExists x A :: Γ, Δ⟩
  | existsR {Γ Δ : Context} (x : Var) (A : Formula) (t : Var) :
      Derivation ⟨Γ, subst x t A :: Δ⟩ → Derivation ⟨Γ, mkExists x A :: Δ⟩

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
