import NfValidate

abbrev Context := List Formula

inductive Derivation : Context → Context → Type
  | ax {Γ Δ : Context} (A : Formula) (hL : A ∈ Γ) (hR : A ∈ Δ) : Derivation Γ Δ
  | exchangeL {Γ Δ : Context} (A B : Formula) :
      Derivation (A :: B :: Γ) Δ → Derivation (B :: A :: Γ) Δ
  | exchangeR {Γ Δ : Context} (A B : Formula) :
      Derivation Γ (A :: B :: Δ) → Derivation Γ (B :: A :: Δ)

def formulaRank : Formula → Nat
  | Formula.atom _ => 0
  | Formula.neg p => formulaRank p + 1
  | Formula.conj p q => max (formulaRank p) (formulaRank q) + 1
  | Formula.disj p q => max (formulaRank p) (formulaRank q) + 1
  | Formula.impl p q => max (formulaRank p) (formulaRank q) + 1
  | Formula.univ _ p => formulaRank p + 1

def derivationHeight {Γ Δ : Context} : Derivation Γ Δ → Nat
  | .ax _ _ _ => 0
  | .exchangeL _ _ d => derivationHeight d + 1
  | .exchangeR _ _ d => derivationHeight d + 1

inductive ReductionError
  | NotImplemented (msg : String)
  deriving Repr

abbrev ReduceResult (Γ Δ : Context) := Except ReductionError (Derivation Γ Δ)

def reduceCut {Γ Δ : Context} (A : Formula) (d1 : Derivation Γ (A :: Δ)) (d2 : Derivation (A :: Γ) Δ) : ReduceResult Γ Δ :=
  match d2 with
  | .exchangeL A2 B2 d2_sub =>
      Except.error (ReductionError.NotImplemented "exchangeL")
  | _ => Except.error (ReductionError.NotImplemented "other")
termination_by (formulaRank A, derivationHeight d1 + derivationHeight d2)

