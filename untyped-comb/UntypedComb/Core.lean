namespace UntypedComb

/--
Topologically-Guided Combinatory AST
Synthesizing Schönfinkel's primitives with Crabbé/Forster T-Weaking.
This entirely bypasses the Calculus of Inductive Constructions, establishing a flat operational domain.
-/
inductive Comb
  | K : Comb -- Schönfinkel's C (Konstanz) / Erasure
  | S : Comb -- Fusion / Duplication
  | I : Comb -- Identity (derivable as S K K, but included for runtime efficiency)
  | U : Comb -- Schönfinkel's Unverträglichkeit (NAND logic for SPE integration)
  | var : String -> Comb
  | app : Comb -> Comb -> Comb
  | t_inject : Comb -> Comb -- The geometric type-shifting endofunctor
  deriving Repr, DecidableEq, Inhabited

end UntypedComb
