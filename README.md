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

#### Extensionality Collisions vs. Strict Global Stratification

Early versions of this repository operated under **strict global stratification**, mechanically verifying Marcel Crabbé's observation that enforcing rigid global typing destroys structural closure under substitution. 

However, evaluating the true systemic paradoxes of New Foundations requires bypassing these trivial syntactic failures. The engine was upgraded to evaluate **weak stratification**. By partitioning the Bellman-Ford graph according to binding scope, local variables can be typed independently. Once dynamic local re-leveling restores substitution closure, the `reduceCut` diagnostic automatically pushes the resolved cuts upward into the active *Extensionality Axiom*. 

The engine actively demonstrates that it is precisely the violent friction between **dynamic local re-leveling** (weak stratification) and **Extensionality's rigid structural equivalence** ($x = y$) that generates the profound normalization breakdown of NF.

### `untyped-comb`: Untyped Combinatory Logic

Standard implementations of the $\lambda$-calculus or combinatory logic in Lean rely heavily on dependent type theory. The `untyped-comb` module constructs an entirely untyped combinatory logic environment and introduces the specific syntactic operators required to make it functional under NF rules. 

By utilizing **Topologically-Guided Lazy Reduction Bounding**, the engine natively compiles operations into a Directed Acyclic Graph (DAG) and algorithmically injects Thomas Forster's T-operator. It leverages Kosaraju's algorithm to flatten semantic cycles and employs Minimum Cycle Mean (MCM) bounds to enforce strict K-Iteration halting limits. This allows the system to execute complex Church Encodings (`CombLib`), including Frege-Russell numerals, transfinite cardinal arithmetic, and paradoxical self-models ($V \in V$) natively without triggering memory exhaustion or relying on an external well-ordering.

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

## Research Applications and Next Steps

This repository serves as a computationally rigorous baseline for exploring the mechanical limits of formal logic under Quine's systemic ambiguity. By drawing on foundational proof theory (Gentzen, Crabbé) and discrete topological routing (Bellman-Ford, Kosaraju), the tools empower researchers to mathematically witness the exact boundaries of a stratified universe without resorting to artificial hierarchies.

With the successful implementation of the `untyped-comb` phase, the project has established the core architectural blueprint for evaluating non-well-founded, self-referential graph geometries.

### Upcoming Milestones

1. **Categorical Semantics (The SPE Architecture)**
   - Transitioning the evaluated logic into applied category theory.
   - Constructing the **Stratified Pseudo Elephant (SPE)** to process a self-referential topology where the universe evaluates its own internal subcategories natively.
   - Implementing **Strongly Cantorian Retractions** as dynamic "islands of classicality," where choice functions and arithmetic can execute safely without triggering negative cycle limits.
2. **Native Systems Execution (The Monist Engine)**
   - Abandoning the dependent type constraints of Lean 4 entirely in favor of a bare-metal implementation written in **Rust**.
   - Compiling the verified Topologically-Guided Lazy Reduction Bounds into **Arena-Allocated Interaction Nets**, optimizing memory traversal for high-performance hardware execution (HVM2/Bend).
   - Establishing real-time execution bounds via dynamic programming and color-coding heuristics to bypass exhaustive path traversal.

## License

This project is licensed under the GNU Affero General Public License v3 (AGPLv3) - see the [LICENSE](LICENSE) file for details.
