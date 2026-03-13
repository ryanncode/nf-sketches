# Parse-Strat: The Interactive Sandbox

This module provides an interactive Read-Eval-Print Loop (REPL) environment for exploring Quine's New Foundations (NF) set theory. It serves as a tactile front-end to the core `nf-validate` logic library.

## Purpose and Scope

While the main `seq-embed` diagnostic tool executes hardcoded, canonical proofs, `parse-strat` is designed for organic exploration. It allows researchers to manually test the boundaries of Quine's systemic ambiguity and observe the mechanical work of the algorithm in real-time without compromising the mathematical integrity of the formal verification suite.

By separating runtime string parsing from compile-time theorem proving, this module provides an exploratory sandbox while keeping the foundational logic pure.

## Features

* **Lexical Scanner & Parser**: Converts raw user input strings into Abstract Syntax Trees (AST). It supports standard first-order logic operators (`~`, `&`, `v`, `->`) and set-theoretic relations (`=`, `e`).
* **Interactive Evaluation**: Users can input multiple formulas to build a conjunction and immediately evaluate the combined structure.
* **Topological Feedback**: The REPL generates the constraint graph, detects cycles, and prints the resulting distance maps (Witness Context) or exact algebraic telescoping sum contradictions.

## Usage

To launch the interactive sandbox, navigate to the `parse-strat` directory and run the executable:

```Bash
lake build
lake exe parse-strat
```

### Example Session

```Plaintext
=== NF Stratification Validator ===
Enter formulas to build a conjunction.
Accepted syntax: Relational statements ('x = y', 'x e y') combined with logical operators ('~', '&', 'v', '->'). Example: '~(x = y) & (y e z)'.
Type 'done' to evaluate the combined formula.
> x e y
> y e z
> z = x
> done

Evaluating constraint graph with DNF conversion and cycle detection...
Result: Not stratifiable. A type contradiction was detected in all branches.
Contradiction Path: x = z (0) → y ∈ z (-1) → x ∈ y (-1).
Requires l(y) = l(x) + -1 and l(y) = l(x) + 1.
```

## Testing

This module also contains the automated test suite (`test_suite.lean`) that verifies the parser's integration with the `nf-validate` core logic.

```Bash
lake env lean test_suite.lean