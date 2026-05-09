# <div align="center">NF Sketches: High-Throughput Combinatory Execution Engine</div>

*A proof-theoretic engine utilizing Lean 4 for* $O(V+E)$ *topological bounds checking to enable acyclic combinatory graph reduction.*

<div align="center">
  <br>
  <a href="https://ryanncode.github.io/nf-sketches/"><strong>📚 Read the Docs</strong></a>
  &nbsp;&nbsp;&nbsp;&nbsp; | &nbsp;&nbsp;&nbsp;&nbsp;
  <a href="https://thing.rodeo/monism/"><strong>🌐 Visit the Blog</strong></a>
  <br><br>
</div>

---

**NF Sketches** provides a bifurcated architecture designed to natively process saturated states, highly entangled sets, and self-referential graph evaluations. By utilizing Lean for $O(V+E)$ topological bounds checking, the engine translates syntax into a Directed Acyclic Graph (DAG). It then algorithmically compiles the verified logic into a flat operational domain of untyped $S$ and $K$ combinators. 

**The Core Motivation:** Traditional set theories and type systems (like Homotopy Type Theory) rely on infinite hierarchical towers of universes (`U0:U1:U2...`) to avoid self-referential paradoxes. This introduces heavy computational friction. **NF Sketches** provides a truly flat alternative based on "Syntactic Monism." The system averts logical collapse by shifting the burden of consistency entirely away from the ontological structure onto the syntax via topological stratification constraints. This allows the logic engine to natively accommodate a Universal Set ($V \in V$) and process reality as a unified, cohesive network without artificial hierarchical scaffolding.

This repository functions as the theoretical **laboratory**—utilizing Lean's trusted kernel to formally prove algorithmic stratification, K-Iteration limits, and topological boundaries. It conducts the rigorous diagnostic work required to secure cryptographic certainty before the concepts are independently forged into the custom bare-metal engine.

---

## Setup and Building

This repository contains multiple interconnected Lean projects. 

### Quick Build
To execute a fast build of a specific module (e.g. the REPL sandbox), navigate to its directory and run:

```bash
lake build
```

### Full Verification Build
Running the `NfValidate` module performs full verification, compiling the entire library along with all 1000+ line soundness proofs. This takes significantly longer as Lean must mathematically verify every theorem:

```bash
lake build NfValidate
```

### Updating Lean and Mathlib

Because these projects rely heavily on `mathlib`, keeping your compiler and cache perfectly synced is critical to avoid multi-hour source compilations. Execute the provided shell script at the root to automate this update process across all projects:

```bash
./update-lean.sh
```

This script syncs the `lean-toolchain`, fetches the latest `mathlib` commit, downloads pre-compiled binaries via `lake exe cache get`, and runs a full build.

### Hello World: Your First Evaluation

Once the project is built, you can immediately test the topological bounds checker using the interactive REPL:

```bash
cd parse-strat
lake env lean Tests/test_suite.lean
```

Alternatively, to explore a topological query interactively:

```bash
lake exe parse-strat
> eval { x | x e x }
```
*(The engine will natively isolate and analyze the recursive boundaries of this comprehension.)*

---

## Core Modules

The repository divides into distinct modules, separating core logical constraints from interactive exploration and bare-metal compilation.

### 1. `nf-validate`: The Core Stratification Library
An algorithmic syntax checker reducing set theory validation into a geometric shortest-path routing problem. Utilizing a modified Bellman-Ford traversal, it mathematically traps non-terminating logical loops as negative-weight cycles, securing a soundness proof entirely independent of traditional model-theoretic structures.

### 2. `parse-strat`: The Interactive ITP Sandbox
A tactile Read-Eval-Print Loop (REPL) environment acting as an Interactive Theorem Prover. It allows users to explore **weak stratification constraints** using classical Natural Deduction tactics (`intro`, `rewrite`, `cut`). By dynamically running `eval`, users can instantly parse topological shift and detect boundaries like Extensionality Collisions in real-time.

### 3. `seq-embed`: The Formal Diagnostic Tool
A deep embedding of Gentzen's Sequent Calculus in Lean that restricts comprehension rules strictly to formulas verified by `nf-validate`. The `reduceCut` engine intentionally forces logical detours through impredicative substitutions (e.g., the Impredicative Singleton or Kuratowski Pair bounds) to mathematically witness normalization breakdowns and graph collapse.

* **Extensionality Collisions**: It verifies Marcel Crabbé's observation that strict global typing destroys substitution closure. By upgrading to **weak stratification**, the engine restores substitution closure but surfaces the **Extensionality Collision**, mathematically proving that classical identity ($x = y$) requires an infinite oracle and otherwise triggers unbounded topological recursion.

### 4. `untyped-comb`: Untyped Combinatory Logic
Constructs a flat, variable-free combinatory execution environment ($S$, $K$, $I$, $U$). 
* **Algorithmic T-Weaking:** Synthesizes Forster's $T$-operator ($x \mapsto \iota"x$) as dynamic geometric stabilizers based on the `NfValidate` integer map.
* **Acyclic Flattening:** Uses Kosaraju's algorithm to flatten semantic cycles.
* **Topologically-Guided Reduction:** Uses Minimum Cycle Mean (MCM) bounds to enforce K-Iteration limits, safely evaluating paradoxical self-reference (like $V \in V$ or the Russell Set) by forcing terminal states without stack exhaustion.

### 5. `CombLib`: Native Operational Semantics
This untyped execution environment processes advanced, paradox-heavy operations natively without memory exhaustion or dependency on external well-ordering axioms:
* **Recursive Self-Models ($V \in V$)**: Uses the Y-combinator to natively evaluate Quine Atoms ($\Omega = \{\Omega\}$), safely relying on MCM halting bounds to intercept infinite topological recursion.
* **Choice-Free Cardinal Arithmetic**: Implements Transfinite Calculus (e.g., $|A| + |B|$ and $\aleph_0$) entirely via pure $\lambda \to S, K$ bracket abstraction, dynamically triggering $T$-functor injections to track disjoint union topologies across structural boundaries.
* **Physical Observables**: Extracts Standard Model empirical metrics (Rest Mass, Resonance) directly from measuring the bounded recursion cost of topological particle knots (`electron_knot`—see the upcoming Speculative Frontier).
* **Holographic Data Indexing**: Compiles absolute complement queries ($V \setminus A$) into $O(1)$ exclusion-first search algorithms, isolating unresolvable contradictions across distributed data swarms in strictly linear time.

### 6. `ExPrograms`: Native Verification
The repository provides a suite of executable Lean scripts that organically evaluate these bounds in real-time logic loops:
* **The Russell Paradox Evaluator**: Geometrically limits $R \in R$.
* **Native Transfinite Arithmetic**: Synthesizes $T$-functor mappings natively on $\aleph_0 + \aleph_0$.
* **Stratified Yoneda Embedding**: Confirms the categorical self-representation natively bounds to $T(F(V))$ without graph collapse, validating Pseudo-Cartesian closure.
* **Agentic Workflows & Simulation**: Evaluates autonomous logic routing via Sandboxed Loops (`AgenticReflection`), and physically calculates Resonance magnitude collisions via `ColliderSimulation` to avoid uncomputable infinities.

---

## License

This project is licensed under the GNU Affero General Public License v3 (AGPLv3) - see the [LICENSE](LICENSE) file for details.
