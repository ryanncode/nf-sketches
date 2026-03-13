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

def substituteVar (x : String) (t : Var) : Var → Var
  | Var.free y => if x == y then t else Var.free y
  | Var.bound i => Var.bound i

def substitute (x : String) (t : Var) : Formula → Formula
  | Formula.atom (Atomic.eq y z) => Formula.atom (Atomic.eq (substituteVar x t y) (substituteVar x t z))
  | Formula.atom (Atomic.mem y z) => Formula.atom (Atomic.mem (substituteVar x t y) (substituteVar x t z))
  | Formula.neg p => Formula.neg (substitute x t p)
  | Formula.conj p q => Formula.conj (substitute x t p) (substitute x t q)
  | Formula.disj p q => Formula.disj (substitute x t p) (substitute x t q)
  | Formula.impl p q => Formula.impl (substitute x t p) (substitute x t q)
  | Formula.univ n p => Formula.univ n (substitute x t p)

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
-- 4. CUT ELIMINATION & NORMALIZATION ENGINE
--------------------------------------------------------------------------------

def formulaRank : Formula → Nat
  | Formula.atom _ => 0
  | Formula.neg p => formulaRank p + 1
  | Formula.conj p q => max (formulaRank p) (formulaRank q) + 1
  | Formula.disj p q => max (formulaRank p) (formulaRank q) + 1
  | Formula.impl p q => max (formulaRank p) (formulaRank q) + 1
  | Formula.univ _ p => formulaRank p + 1

def derivationHeight {Γ Δ : Context} : Derivation ⟨Γ, Δ⟩ → Nat
  | .ax _ _ _ => 0
  | .weakenL _ d => derivationHeight d + 1
  | .weakenR _ d => derivationHeight d + 1
  | .contractL _ d => derivationHeight d + 1
  | .contractR _ d => derivationHeight d + 1
  | .exchangeL _ _ d => derivationHeight d + 1
  | .exchangeR _ _ d => derivationHeight d + 1
  | .cut _ d1 d2 => max (derivationHeight d1) (derivationHeight d2) + 1
  | .conjL _ _ d => derivationHeight d + 1
  | .conjR _ _ d1 d2 => max (derivationHeight d1) (derivationHeight d2) + 1
  | .disjL _ _ d1 d2 => max (derivationHeight d1) (derivationHeight d2) + 1
  | .disjR _ _ d => derivationHeight d + 1
  | .implL _ _ d1 d2 => max (derivationHeight d1) (derivationHeight d2) + 1
  | .implR _ _ d => derivationHeight d + 1
  | .negL _ d => derivationHeight d + 1
  | .negR _ d => derivationHeight d + 1
  | .univL _ _ _ d => derivationHeight d + 1
  | .univR _ _ _ _ _ d => derivationHeight d + 1
  | .existsL _ _ _ _ _ d => derivationHeight d + 1
  | .existsR _ _ _ d => derivationHeight d + 1
  | .extensionality => 0
  | .compL _ _ _ _ _ => 0

inductive ReductionError
  | StratificationFailure (msg : String)
  | NotImplemented (msg : String)
  deriving Repr

abbrev ReduceResult (Γ Δ : Context) := Except ReductionError (Derivation ⟨Γ, Δ⟩)

set_option linter.unusedVariables false

def reduceCut {Γ Δ : Context} (A : Formula) (d1 : Derivation ⟨Γ, A :: Δ⟩) (d2 : Derivation ⟨A :: Γ, Δ⟩) : ReduceResult Γ Δ :=
  match d2 with
  | .compL n_x n_y phi w h_strat =>
      -- Stratification Break Diagnostic
      -- We simulate a substitution into phi that might break stratification.
      let phi_subst := substitute "x" (Var.free "y") phi
      match checkStrat phi_subst with
      | none => Except.error (ReductionError.StratificationFailure "Stratification broken on substitution")
      | some _ => Except.error (ReductionError.NotImplemented "compL reduction not fully implemented")
  | .weakenL A2 d2_sub =>
      -- Principal reduction for weakenL: A was weakened, we can just return d2_sub.
      -- A2 is unified with A.
      Except.ok d2_sub
  | .conjL A2 B2 d2_sub =>
      match d1 with
      | .conjR _ _ d1_A d1_B =>
          have h1 : formulaRank B2 < formulaRank (Formula.conj A2 B2) := by
            simp [formulaRank]
            omega
          have h2 : formulaRank A2 < formulaRank (Formula.conj A2 B2) := by
            simp [formulaRank]
            omega
          do
            let cut_B ← reduceCut B2 (.weakenL A2 d1_B) (.exchangeL A2 B2 d2_sub)
            reduceCut A2 d1_A cut_B
      | .weakenR _ d1_sub =>
          Except.ok d1_sub
      | _ => Except.error (ReductionError.NotImplemented "Other reductions not implemented")
  | .disjL A2 B2 d2_A d2_B =>
      match d1 with
      | .disjR _ _ d1_sub =>
          have h1 : formulaRank A2 < formulaRank (Formula.disj A2 B2) := by
            simp [formulaRank]
            omega
          have h2 : formulaRank B2 < formulaRank (Formula.disj A2 B2) := by
            simp [formulaRank]
            omega
          do
            let cut_A ← reduceCut A2 d1_sub (.weakenR B2 d2_A)
            reduceCut B2 cut_A d2_B
      | .weakenR _ d1_sub =>
          Except.ok d1_sub
      | _ => Except.error (ReductionError.NotImplemented "Other reductions not implemented")
  | .implL A2 B2 d2_A d2_B =>
      match d1 with
      | .implR _ _ d1_sub =>
          have h1 : formulaRank A2 < formulaRank (Formula.impl A2 B2) := by
            simp [formulaRank]
            omega
          have h2 : formulaRank B2 < formulaRank (Formula.impl A2 B2) := by
            simp [formulaRank]
            omega
          do
            let cut_A ← reduceCut A2 (.exchangeR B2 A2 (.weakenR B2 d2_A)) d1_sub
            reduceCut B2 cut_A d2_B
      | .weakenR _ d1_sub =>
          Except.ok d1_sub
      | _ => Except.error (ReductionError.NotImplemented "Other reductions not implemented")
  | _ =>
      match d1 with
      | .weakenR _ d1_sub =>
          Except.ok d1_sub
      | _ => Except.error (ReductionError.NotImplemented "Other reductions not implemented")
termination_by (formulaRank A, derivationHeight d1 + derivationHeight d2)

--------------------------------------------------------------------------------
-- 5. BASIC INPUT/OUTPUT EXECUTABLE
--------------------------------------------------------------------------------

def main : IO Unit := do
  IO.println "=== Stratified Sequent Calculus Environment ==="
  IO.println "Environment initialized with locally nameless AST and Gentzen rules."
