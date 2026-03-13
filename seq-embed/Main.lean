import NfValidate

--------------------------------------------------------------------------------
-- 1. SEQUENT DEFINITION & SYNTACTIC SUGAR
--------------------------------------------------------------------------------

abbrev Context := List Formula

structure Sequent where
  gamma : Context -- Antecedents (Left)
  delta : Context -- Succedents (Right)
  deriving Repr, BEq

-- Syntactic sugar for biconditional and existential quantification
def mkIff (p q : Formula) : Formula :=
  Formula.conj (Formula.impl p q) (Formula.impl q p)

def mkExists (n : String) (p : Formula) : Formula :=
  Formula.neg (Formula.univ n (Formula.neg p))

-- Constructs the NF Comprehension Axiom body: ∃x ∀y (y ∈ x ↔ φ)
-- In locally nameless, inside ∀y, y is `bound 0` and x is `bound 1`.
def mkComprehensionAxiom (n_x n_y : String) (phi : Formula) : Formula :=
  mkExists n_x (Formula.univ n_y (mkIff (Formula.mem (Var.bound 0) (Var.bound 1)) phi))

-- Constructs the Extensionality Axiom: ∀x ∀y (∀z (z ∈ x ↔ z ∈ y) → x = y)
-- Inside ∀z, z is `bound 0`, y is `bound 1`, x is `bound 2`.
def mkExtensionalityAxiom : Formula :=
  Formula.univ "x" (Formula.univ "y" (Formula.impl
    (Formula.univ "z" (mkIff (Formula.mem (Var.bound 0) (Var.bound 2)) (Formula.mem (Var.bound 0) (Var.bound 1))))
    (Formula.eq (Var.bound 1) (Var.bound 0))))

--------------------------------------------------------------------------------
-- LOCALLY NAMELESS SUBSTITUTION & FRESH VARIABLES
--------------------------------------------------------------------------------

def freeVarsVar : Var → List Var
  | Var.free x => [Var.free x]
  | Var.bound _ => []

def freeVars : Formula → List Var
  | Formula.atom (Atomic.eq y z) => freeVarsVar y ++ freeVarsVar z
  | Formula.atom (Atomic.mem y z) => freeVarsVar y ++ freeVarsVar z
  | Formula.neg p => freeVars p
  | Formula.conj p q => freeVars p ++ freeVars q
  | Formula.disj p q => freeVars p ++ freeVars q
  | Formula.impl p q => freeVars p ++ freeVars q
  | Formula.univ _ p => freeVars p

def openVar (k : Nat) (t : Var) (v : Var) : Var :=
  match v with
  | Var.bound i => if i == k then t else v
  | Var.free _ => v

def openFormula (k : Nat) (t : Var) : Formula → Formula
  | Formula.atom (Atomic.eq y z) => Formula.atom (Atomic.eq (openVar k t y) (openVar k t z))
  | Formula.atom (Atomic.mem y z) => Formula.atom (Atomic.mem (openVar k t y) (openVar k t z))
  | Formula.neg p => Formula.neg (openFormula k t p)
  | Formula.conj p q => Formula.conj (openFormula k t p) (openFormula k t q)
  | Formula.disj p q => Formula.disj (openFormula k t p) (openFormula k t q)
  | Formula.impl p q => Formula.impl (openFormula k t p) (openFormula k t q)
  | Formula.univ n p => Formula.univ n (openFormula (k + 1) t p)

def instantiate (t : Var) (f : Formula) : Formula := openFormula 0 t f

--------------------------------------------------------------------------------
-- 2. STRATIFIED SEQUENT CALCULUS
--------------------------------------------------------------------------------

-- Derivations are modeled as an inductive family indexed by Sequents.
inductive Derivation : Sequent → Type
  -- Identity
  | ax {Γ Δ : Context} (A : Formula) (hL : A ∈ Γ) (hR : A ∈ Δ) : Derivation ⟨Γ, Δ⟩

  -- Structural Rules
  | weakenL {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, Δ⟩ → Derivation ⟨A :: Γ, Δ⟩
  | weakenR {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, Δ⟩ → Derivation ⟨Γ, A :: Δ⟩

  | contractL {Γ Δ : Context} (A : Formula) :
      Derivation ⟨A :: A :: Γ, Δ⟩ → Derivation ⟨A :: Γ, Δ⟩
  | contractR {Γ Δ : Context} (A : Formula) :
      Derivation ⟨Γ, A :: A :: Δ⟩ → Derivation ⟨Γ, A :: Δ⟩

  | exchangeL {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨A :: B :: Γ, Δ⟩ → Derivation ⟨B :: A :: Γ, Δ⟩
  | exchangeR {Γ Δ : Context} (A B : Formula) :
      Derivation ⟨Γ, A :: B :: Δ⟩ → Derivation ⟨Γ, B :: A :: Δ⟩

  -- The Cut Rule
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
  | univL {Γ Δ : Context} (n : String) (A : Formula) (t : Var) :
      Derivation ⟨instantiate t A :: Γ, Δ⟩ → Derivation ⟨Formula.univ n A :: Γ, Δ⟩
  | univR {Γ Δ : Context} (n : String) (A : Formula) (y : String)
      (h_fresh_gamma : ∀ F ∈ Γ, Var.free y ∉ freeVars F)
      (h_fresh_delta : ∀ F ∈ Δ, Var.free y ∉ freeVars F) :
      Derivation ⟨Γ, instantiate (Var.free y) A :: Δ⟩ → Derivation ⟨Γ, Formula.univ n A :: Δ⟩

  -- Logical Rules: Existential Quantification
  | existsL {Γ Δ : Context} (n : String) (A : Formula) (y : String)
      (h_fresh_gamma : ∀ F ∈ Γ, Var.free y ∉ freeVars F)
      (h_fresh_delta : ∀ F ∈ Δ, Var.free y ∉ freeVars F) :
      Derivation ⟨instantiate (Var.free y) A :: Γ, Δ⟩ → Derivation ⟨mkExists n A :: Γ, Δ⟩
  | existsR {Γ Δ : Context} (n : String) (A : Formula) (t : Var) :
      Derivation ⟨Γ, instantiate t A :: Δ⟩ → Derivation ⟨Γ, mkExists n A :: Δ⟩

  ------------------------------------------------------------------------------
  -- 3. SET-THEORETIC AXIOMS
  ------------------------------------------------------------------------------

  -- Extensionality Axiom
  | extensionality {Γ Δ : Context} :
      Derivation ⟨mkExtensionalityAxiom :: Γ, Δ⟩

  -- Restricted Comprehension Rule
  -- Gated by the pure stratification validator from NfValidate.
  | compL {Γ Δ : Context} (n_x n_y : String) (phi : Formula) (w : StratificationWitness)
      (h_strat : checkStrat phi = some w) :
      Derivation ⟨mkComprehensionAxiom n_x n_y phi :: Γ, Δ⟩

--------------------------------------------------------------------------------
-- 4. BASIC INPUT/OUTPUT EXECUTABLE
--------------------------------------------------------------------------------

def main : IO Unit := do
  IO.println "=== Stratified Sequent Calculus Environment ==="
  IO.println "Environment initialized with locally nameless AST and Gentzen rules."
