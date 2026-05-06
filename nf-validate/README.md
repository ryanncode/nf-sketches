# NF-Validate: Core NF Logic Stratification Library

A mathematical validation engine for Quine's New Foundations (NF) set theory. This Lean library evaluates logical formulas to determine structural soundness and stratifiability. Built as a "compiler-as-witness," the codebase strictly translates abstract philosophical logic into machine-readable syntax, subsequently mathematically guaranteeing its own accuracy through dependent type theory.

## Philosophical Explication: The Grammar of Sets

In standard Zermelo-Fraenkel set theory, paradoxical sets are avoided through the iterative conception of set formation, often modeled via an unbounded cumulative hierarchy. Quine's New Foundations (NF) takes a radically different approach. Stratification is an entirely grammatical constraint.

In NF, a logical formula is considered stratifiable if and only if one can assign an integer "type level" to every variable such that:

1. For every equality $x = y$, their assigned levels are identical: $l(x) = l(y)$.
2. For every membership relation $x ∈ y$, the level of the right side is exactly one greater than the left: $l(y) = l(x) + 1$.

By approaching set theory as a structural proof problem, this validator avoids redundant model-theoretic iterative hierarchies. The operational focus shifts entirely to executing logic as a mechanical, syntactic process. The engine acts as an algorithmic syntax checker, operationalizing the systematic ambiguity of the language.

## Architecture

The software architecture is structured as a continuous mathematical proof. The transition from abstract syntax evaluation to graph-theoretic verification is rigorously certified within the Lean environment.

### 1. Abstract Syntax Tree (AST) Bifurcation

The foundational data structure strictly separates standard propositional connectives from domain-specific set-theoretic primitives using a locally nameless representation.

Standard variable substitution functions well across normal logical connectives during semantic truth evaluations. Passing complex terms into atomic relations, however, triggers the dynamic shifts in relative type assignments unique to NF. By sequestering the `eq` and `mem` relations within a dedicated Atomic type, the system isolates the precise operational bottleneck where classical first-order logic mechanisms break down under restricted syntactic constraints.

### 2. DNF Reduction and Constraint Generation

Complex, branching logical statements are algorithmically flattened into Disjunctive Normal Form (DNF). The validator distributes conjunctions over disjunctions and pushes negations down to the atomic level using verified implementations of De Morgan's laws.

Once flattened, the formula is translated into a series of directed subgraphs. Rather than forcing a single monolithic type assignment across the entire formula (strict global stratification), the constraints are partitioned by **quantifier scope**, establishing the mathematical baseline for **Weak Stratification**. The grammatical rules of NF are converted into integer difference inequalities:

* $x ∈ y$ generates a forward edge $(x, y)$ with weight 1 and a backward edge $(y, x)$ with weight -1.
* $x = y$ generates bidirectional zero-weight edges.

### 3. The Bellman-Ford Evaluator

The system processes the generated constraints using a verified implementation of the Bellman-Ford algorithm.

If the logic is grammatically consistent, the traversal computes the shortest paths and produces a minimal valid numbering system (a "witness" context). If the logic contains a paradox (e.g., the cyclical constraint $x ∈ x$, requiring $l(x) = l(x) + 1$), the algorithm detects a negative-weight cycle and rigorously extracts the contradiction path.

### 4. Mathematical Certification (The Soundness Proofs)

The most critical feature of this codebase is its self-verification. The compiler mechanically checks its own proofs to guarantee that the cycle-detection logic perfectly executes the grammatical rules of the targeted logic system.

* **Bounded Convergence:** The implementation leverages structural induction to verify that edge relaxation strictly preserves monotonicity and terminates within $|V|-1$ iterations.
* **Combinatorial Extraction:** Relying on Lean's Mathlib, the system applies the Pigeonhole Principle to prove that any continuously updating path traversing beyond the graph's vertex cardinality mathematically guarantees a geometric cycle.
* **Algebraic Contradiction:** To bypass dependent-type unification deadlocks inherent to indexed path slicing, the validator employs a list projection strategy. It utilizes a telescoping sum over the extracted edge list. Because the loop is closed, mapped vertex distances algebraically cancel to zero, definitively proving that the subset of constraints generating the cycle possesses a total weight strictly less than zero.

## Note on I/O and Interactive Use

To maintain its purity as a strict logical library, `nf-validate` contains no runtime string parsing or interactive REPL features. All interactive parsing, execution loops, and test suites are located in the dedicated `parse-strat` module.

## Compilation and Execution

The system requires the standard Lean 4 toolchain and Mathlib.

### 1. Library Verification
To strictly compile the mathematical library and mechanically verify all geometric soundness proofs:

```Bash
lake build NfValidate
```

### 2. The NFI vs. NFP Diagnostic
The primary executable runs an automated diagnostic evaluating the structural bounds of the Natural Numbers against the disparate predicative (NFP) and impredicative (NFI) typings of NF.

To execute the diagnostic:

```Bash
lake build nf-validate
./.lake/build/bin/nf-validate
```

### 3. Algorithmic Profiling
The `profile-acyclic` executable benchmarks the performance of AST compilation and the $O(N^2)$ geometric graph validators. It specifically targets the evaluation of weak stratification bounds utilizing Kosaraju's algorithm against massive matrices of disjoint and deeply connected components.

To run the profiler:

```Bash
lake build profile-acyclic
./.lake/build/bin/profile-acyclic
```