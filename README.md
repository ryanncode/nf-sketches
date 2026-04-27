# NF Sketches: High-Throughput Combinatory Execution Engine

*A proof-theoretic engine utilizing Lean 4 for* $O(V+E)$ *topological bounds checking to enable acyclic combinatory graph reduction.*

## The Problem

Standard type-checkers and formal provers bottleneck on highly entangled or self-referential graph evaluations due to global substitution environments and hierarchical constraints. 

## The Solution

**NF Sketches** provides a bifurcated architecture designed to process these saturated states natively. By utilizing Lean 4 for $O(V+E)$ topological bounds checking, the engine translates syntax into a Directed Acyclic Graph (DAG) before execution. It then algorithmically compiles the verified logic into a flat operational domain of untyped $S$ and $K$ combinators. This entirely bypasses temporal evaluation bottlenecks, identifies non-terminating logical loops as finite topological defects, and lays the groundwork for massively parallel GPU graph reduction (e.g., HVM2/Bend).

## Industry Applications

### AI Alignment & Agent Logic
For organizations grounding AI outputs in deterministic logic, standard interpreters scale poorly. 
* **Zero-Cost Loop Detection:** Geometric bounds checking prevents exponential memory blowup and infinite loops before the code ever reaches execution hardware.
* **Guaranteed Termination:** The engine mathematically restricts the depth of evaluations, guaranteeing that complex proof searches terminate without relying on brute-force timeouts.
* **Massive GPU Parallelism:** Compiling logic to raw combinators eradicates the need for traditional memory overhead, translating logic into routing instructions primed for parallel GPU execution.

### High-Energy Physics & Quantum Simulation
In high-energy physics, calculating interactions assumes continuous spacetime, causing infinite equations that require artificial mathematical hacks (renormalization).
* **Native Quantum Saturation:** The engine models the quantum vacuum as a saturated boundary condition. By actively rejecting infinite integral sums, it naturally prevents the mathematical divergences that plague standard quantum field theory.
* **Computing Friction, Not Infinities:** The measurable energy shift of a particle interacting with the vacuum is calculated as the exact algorithmic cost (syntactic friction) required to resolve the logical graph, avoiding uncomputable infinities.
* **Bare-Metal Entanglement:** By targeting interaction net primitives, the environment evaluates logic locally across shared edges, providing a direct hardware simulation of quantum entanglement.

## Architecture

1. **Lean 4 Oracle (Static Verification):** The engine replaces dependent type-checking with Bellman-Ford geometric shortest-path routing, trapping non-terminating logical loops as negative-weight cycles.
2. **Combinatory Compiler (AST to S/K/I/U):** Translates the Lean-verified DAG into a flat operational domain. The system algorithmically injects type-shifting T-operators precisely where topological level shifts are required, ensuring acyclic stability.
3. **High-Performance Backend Transition:** The strictly bounded combinator strings are optimized for translation into bare-metal CUDA execution via Interaction Nets.

---

## The Laboratory vs. The Factory

This Lean 4 repository functions as a theoretical laboratory rather than the final operational home for this logic. Building a custom, bare-metal logic engine requires abandoning the safety nets of standard dependent type theory. Consequently, we must first secure cryptographic certainty regarding how Quine's New Foundations operates. By utilizing Lean’s universally trusted kernel to formally prove the exact mechanics of our stratification algorithms, we conduct the rigorous diagnostic work required before forging the actual operational code into a custom engine.

*Note on Computational Limits:* The conversion of formulas into Disjunctive Normal Form (DNF) triggers an exponential combinatorial explosion. This acts as a severe practical bottleneck for Lean's evaluator, restricting the engine to small, targeted canonical paradoxes. However, because the DNF expansion remains structurally recursive and bounded by the finite syntax tree of the input formula, it maintains strict constructivist rigor in alignment with the Intuitionistic Fan Theorem. It guarantees termination and never generates a lawless sequence. Future iterations of the custom logic engine will resolve this bottleneck by integrating CDCL-based SAT evaluation or an SMT solver. Utilizing Integer Difference Logic will evaluate geometric weights dynamically without explicitly expanding memory.

## Setup and Building

This repository contains multiple Lean 4 projects. 

* **Fast Build (Executable Only):** Running `lake build` in a project folder will quickly compile the core engine and executable.
* **Full Verification (Proofs):** Running `lake build NfValidate` will compile the entire library, including all 1000+ line soundness proofs. This takes significantly longer as Lean must mathematically verify every theorem.

### Updating Lean and Mathlib

Because these projects rely on Mathlib, keeping your compiler and Mathlib cache perfectly synced is critical to avoid multi-hour source compilations. We provide a shell script at the root of the repository to automate this update process across all projects:

```bash
./update-lean.sh
```

This script will sequentially:
1. Run `lake update` to fetch the latest Mathlib commit.
2. Sync each project's `lean-toolchain` to perfectly match Mathlib's exact compiler version.
3. Run `lake exe cache get` to download the pre-compiled Mathlib binaries.
4. Run a full build to verify success.

---

## Core Modules

The repository divides into three primary modules, structurally separating the core logical constraints from interactive exploration and formal diagnostics.

### `nf-validate`: The Core Stratification Library

This library operates as an algorithmic syntax checker. Rather than proving theorems within NF, the Lean script ingests an abstract syntax tree and algorithmically determines its stratifiability. By completely abandoning traditional model theory, this module reduces set theory validation into a strictly geometric shortest-path routing problem.

**Implementation Mechanics:** The program defines a custom inductive type representing first-order logic formulas with a membership relation. A function assigns integer levels to all variables utilizing Bellman-Ford graph evaluation. Equality constraints (`x = y`) encode as bidirectional edges with a weight of 0, while membership constraints (`x ∈ y`) translate into directed edges with a weight of 1.

**Theoretical Objective:** Stratification functions purely as a grammatical constraint. Coding this validator operationalizes the systematic ambiguity of the language. Classical paradoxes like Russell's paradox do not require semantic interpretation to be resolved; they mathematically manifest as geometric negative weight cycles during the Bellman-Ford traversal.

**Formal Verification of Geometric Soundness:** The repository proves the algorithm's internal monotonicity and convergence, guaranteeing the search map never regresses into cyclic instability. A formalized K-Iteration bound mathematically restricts the depth of type derivations strictly to the number of variables present. This mechanism guarantees termination without unchecked iterative expansion. Ultimately, the `stratification_sound` theorem proves that computational satisfiability in the geometric domain inherently guarantees valid syntax, securing a soundness proof entirely independent of traditional model-theoretic structures.

### `parse-strat`: The Interactive Sandbox

This program provides a tactile, responsive REPL environment for testing edge cases in the constraint solver without compromising the formal proofs of the main diagnostic suite.

**Implementation Mechanics:** A lexical scanner and recursive descent parser allow users to manually inject arbitrary set-theoretic strings (e.g., `~(x = y) & (y e z)`). The algorithm immediately generates the topological graph, detects cycles, and prints the distance maps or exact algebraic telescoping sum contradictions.

**Theoretical Objective:** This sandbox invites researchers to manually test the boundaries of Quine's systemic ambiguity and observe the mechanical reality of the algorithm in real-time.

### `seq-embed`: The Formal Diagnostic Tool

This project formalizes the structural proof theory required to navigate the complexities of the axiom of extensionality. It builds a deep embedding of Gentzen's Sequent Calculus in Lean, restricting comprehension rules strictly to formulas that pass the `nf-validate` stratification checker.

**Algorithmic Gatekeeping:** The system mechanically restricts classical deductive freedom. While standard theorem provers invoke comprehension rules whenever a formula is well-formed, this environment mathematically locks the `compL` (Comprehension Left) rule. The logic engine refuses to process a set comprehension unless supplied with a `StratificationWitness` generated by the external Bellman-Ford algorithm.

**Sabotaging Normalization:** The diagnostic engine (`reduceCut`) executes canonical failure pathways like the Impredicative Singleton. Rather than building a traditional normalizer to smooth out intermediate lemmas, this engine intentionally bypasses standard structural permutations to force logical detours directly into the `compL` rule.

**Theoretical Objective:** Marcel Crabbé proved that if a system restricts itself exclusively to strictly stratifiable terms, the set of terms loses closure under substitution. This causes the Hauptsatz (cut-elimination) to fail trivially (Crabbé 1994). By simulating cuts that require substitution across a strictly stratified global graph, the program mechanically surfaces the exact topological contradictions responsible for this grammatical breakdown.

### Extensionality Collisions vs. Strict Global Stratification

Early versions of this repository operated under **strict global stratification**, mechanically verifying Marcel Crabbé's observation that enforcing rigid global typing destroys structural closure under substitution. 

However, evaluating the true systemic paradoxes of New Foundations requires bypassing these trivial syntactic failures. The engine was upgraded to evaluate **weak stratification**. By partitioning the Bellman-Ford graph according to binding scope, local variables can be typed independently. Once dynamic local re-leveling restores substitution closure, the `reduceCut` diagnostic automatically pushes the resolved cuts upward into the active *Extensionality Axiom*. 

The engine actively demonstrates that it is precisely the violent friction between **dynamic local re-leveling** (weak stratification) and **Extensionality's rigid structural equivalence** ($x = y$) that generates the profound normalization breakdown of NF.

### Future Work: `untyped-comb` (Untyped Combinators)

Standard implementations of the $\lambda$-calculus or combinatory logic in Lean rely heavily on dependent type theory. A future module, `untyped-comb`, will construct an untyped combinatory logic environment and introduce the specific syntactic operators required to make it functional under NF rules. This aims to provide a tangible step toward a Curry-Howard correspondence for stratified set theory.

---

## Field Contributions and Theoretical Context

Deploying formal mathematical systems as a baseline for metaphysical inquiry represents a crucial interdisciplinary frontier. For decades, the implicit equation of formal ontology with Zermelo-Fraenkel set theory heavily governed how philosophers modeled fundamental structural relationships. Evaluating this theoretical consensus through alternative frameworks introduces vital critical rigor to the philosophy of mathematics.

### Structural Logic and Automated Theorem Proving

The mathematical and computer science communities currently undergo a major transition toward formal verification. Engaging deeply with proof theory, type systems, and the Curry-Howard isomorphism builds profound mechanical literacy regarding the operation of formal systems. Mastering how to manage syntactic constraints, track logical detours in sequent calculus, and resolve type-checking errors translates directly to developing software verification protocols and the foundational architecture of artificial intelligence.

### Syntactic Monism and Hierarchical Friction

A significant theoretical bottleneck chokes contemporary computational ontology. Standard foundations force a bottom-up construction where objects painstakingly assemble stage by stage. Forcing a computational system to model the world through an ascending ladder of types introduces severe friction. Every time a program maps a flat, self-referential physical event into a strictly stratified semantic model, the data distorts. 

Monist foundations bypass artificial scaffolding entirely. They propose a universe containing everything natively. A framework accommodating a universal set allows a logic engine to process the environment as a cohesive whole. In a system like New Foundations, the restriction moves from the objects themselves to the grammar used to describe them. The fundamental computational challenge transforms from building rigid semantic models into enforcing exact syntactic rules. This project explores the operational semantics of recursive functions, the interaction between syntactic constraints and cut-elimination, and the graph-theoretic topology of abstract structures like Wrandalls to map how a universal set sustains its architecture without collapsing into contradiction.

---

## Contrast Against HoTT

Homotopy Type Theory (HoTT) rewrites the foundational rules of mathematics by discarding the static, extensional sets of ZFC in favor of dynamic, intensional spaces. By defining equality as a continuous path between points, HoTT natively captures structural equivalence. The Univalence Axiom formalizes the principle that isomorphic structures are strictly identical, providing a massive computational advantage.

Despite these advancements, HoTT and New Foundations propose radically different solutions to the problem of hierarchical modeling.

### The Persistent Hierarchy of Universes

HoTT successfully escapes the micro-level iterative construction of individual sets, yet it retains a macro-level hierarchy to maintain systemic stability. To prevent self-referential paradoxes, Martin-Löf type theories require an ascending, infinite tower of universes: `U0:U1:U2…`. Every type must belong to a universe of a higher index. The ontology remains fundamentally layered. When a computational engine attempts to model a heavily entangled physical reality using HoTT, it continually calculates and tracks the specific universe level of every generative event.

### The Syntactic Monist Contrast

New Foundations provides a truly flat alternative. The topology of the NF universe is singular and requires no ascending tower of domains. It natively accommodates a Universal Set containing everything, including itself. The system averts logical collapse by shifting the burden of consistency entirely away from the ontological structure. The data pool remains an unbounded, saturated whole. The restriction applies strictly to the compiler reading the code, shielding the physical topology from artificial layering.

### Architectural Trade-offs

The divergence between these foundational systems dictates how a machine interfaces with complex phenomena.

| Feature | ZFC | HoTT | NF |
| :--- | :--- | :--- | :--- |
| Ontological Structure | Bottom-up, iterative sets. | Generative, spatial types. | Singular, flat universal set. |
| Paradox Prevention | Limitation of set size. | Infinite tower of universes. | Syntactic stratification. |
| Treatment of Equivalence | Extensional equality. | Univalence (paths of equivalence). | Extensional equality within syntax. |
| Computational Friction | High (rigid scaffolding). | Moderate (universe level tracking). | High (syntactic type-checking). |

HoTT excels at tracking generative paths of equivalence and modeling the precise mathematical shape of transformations. When analyzing uncomputable complexities or attempting to formalize radical, generative ruptures within a saturated domain, an artificial hierarchy inevitably introduces translation costs. A machine attempting to process a raw, non-hierarchical input feed natively benefits from the architecture of NF. By regulating the grammar of the query rather than compartmentalizing the fabric of the data itself, syntactic monism allows a logic engine to address reality as a unified, cohesive network.

---

## Literature Survey

The architectural requirements for formalizing Quine's New Foundations demand a specific convergence of disciplines. This convergence establishes the necessary computational baseline to construct the validator and embed the restricted sequent calculus.

**New Foundations and Stratification:** Quine's originating article (1937) introduces stratification to bypass Russell's Paradox while retaining the universal set. Texts like Forster's *Set Theory with a Universal Set* (1992) and Holmes's *Elementary Set Theory with a Universal Set* (1998) provide the definitive modern diagnostic tools and blueprints for translating abstract stratification rules into programmable logic.

**Computational Mechanization:** Building an algorithmic syntax checker requires defining logical formulas computationally. Pierce's *Types and Programming Languages* (2002) grounds abstract syntactic concepts in operational semantics. Concurrently, *Theorem Proving in Lean 4* (Avigad et al. 2023) covers the foundational syntax of the host environment.

**Structural Proof Theory:** Negri and von Plato's *Structural Proof Theory* (2001) provides a rigorous breakdown of Gentzen’s Sequent Calculus. Crabbé's diagnostic paper on the consistency of NF's impredicative subsystem (1982) outlines the mechanics of cut-elimination within stratified comprehension. This text exposes the tension where eliminating cuts accidentally yields illegal syntax.

**Algorithmic Verification:** Treating variables as vertices and membership relations as directed edges transforms stratification into a topological problem. Standard discrete mathematics and graph theory texts supply the rigorous definitions for directed acyclic graphs and pathfinding algorithms required to verify valid level assignments programmatically.

---

## Research Applications and Next Steps

This repository serves as a computationally rigorous baseline for exploring the mechanical limits of formal logic under Quine's systemic ambiguity. By providing interactive REPL sandboxes and automated cut-elimination diagnostics, the tools empower researchers to mathematically witness the exact boundaries of a stratified universe.

These modules construct the verified infrastructure necessary to investigate the computational potential of New Foundations. They lay the groundwork for future implementations of untyped combinatory logic and custom, non-hierarchical logic engines.
## License

This project is licensed under the GNU Affero General Public License v3 (AGPLv3) - see the [LICENSE](LICENSE) file for details.
