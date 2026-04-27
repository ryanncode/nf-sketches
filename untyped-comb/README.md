# Untyped Combinatory Logic (`untyped-comb`)

The `untyped-comb` module serves as the bare-metal combinatory execution phase of the `nf-sketches` architecture. It systematically formalizes Quine's New Foundations (NF) logic not through classical dependent types or global hierarchies, but via raw, variable-free operational syntax.

## Overview

This Lean 4 module bypasses the Calculus of Inductive Constructions to establish a flat operational domain. By applying Moses Schönfinkel and Haskell Curry's combinators ($S$, $K$, $I$, $U$), the system maps Extensionality Collisions natively.

Standard execution of highly saturated impredicative sets (e.g., $V \in V$) exhausts memory boundaries due to unbounded recursion. `untyped-comb` solves this through:

1. **Algorithmic T-Weaking**: Implementing Thomas Forster's $T$-operator ($x \mapsto \iota"x$) as a topological geometric distance map that algorithmically shifts implicit type levels to stabilize the expression.
2. **Acyclic Combinatorial Translation**: Using Directed Acyclic Graphs (DAGs) and Kosaraju's algorithm to identify strongly connected components (SCCs) and securely flatten non-well-founded logical regressions into stabilized terminals.
3. **Topologically-Guided Lazy Reduction**: Applying explicit `lazy_thunk` abstractions combined with Minimum Cycle Mean (MCM) approximation to establish firm K-Iteration halting limits, ensuring the system registers paradoxical self-reference as a terminal state without crashing.
4. **Combinatory Executable Standard Library (`CombLib`)**: A suite of Church-encoded primitives proving the engine's Turing completeness.
   - **Inductive Types**: Direct node-collision topologies mapping boolean logic, arithmetic (`succ`, `add`, `mult`), and inductive lists (`cons`, `head`, `tail`).
   - **Self-Models**: Applying the Y-Combinator to construct models of Quine atoms ($\Omega = \{\Omega\}$) and the universal set ($V \in V$).
   - **Frege-Russell Numerals**: Modeling cardinality via properties of sets.
   - **Transfinite Cardinal Arithmetic**: Setting the foundation for native operations on Aleph limits bypassing the Axiom of Choice.

## Build and Run

To compile the codebase and run the tests (which evaluate safe halting of recursive models and DAG acyclic flattening):

```bash
cd untyped-comb
lake build
```

All combinatory limits and logical evaluations are formally verified natively within Lean's runtime.