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

## The Problem

Standard type-checkers and formal provers bottleneck on highly entangled or self-referential graph evaluations due to global substitution environments and hierarchical constraints. 

## The Solution

**NF Sketches** provides a bifurcated architecture designed to process these saturated states natively. By utilizing Lean 4 for $O(V+E)$ topological bounds checking, the engine translates syntax into a Directed Acyclic Graph (DAG) before execution. It then algorithmically compiles the verified logic into a flat operational domain of untyped $S$ and $K$ combinators. This entirely bypasses temporal evaluation bottlenecks, identifies non-terminating logical loops as finite topological defects, and lays the groundwork for massively parallel GPU graph reduction (e.g., HVM2/Bend).

## Industry Applications

### Holographic Database Structures

Because the engine supports operations on the absolute complement, it enables the creation of holographic database architectures that map queries as spatial constraints rather than iterative lists. By evaluating exclusion-first logic gates over a distributed network, the engine can return valid dataset intersections in $O(1)$ time. This eliminates standard search indexing overhead and enables instantaneous pattern matching across massively saturated, unstructured data lakes.

### Custom Hardware Integration

Standard processors (CPUs/GPUs) are optimized for sequential arithmetic, creating a von Neumann bottleneck for highly entangled, self-referential logic. By compiling NF logic down to fundamental untyped combinators, this engine provides the precise spatial blueprints required for custom ASIC or FPGA hardware development. Physical microprocessors can be patterned directly after Interaction Net topologies, creating chips where "memory" and "processing" are unified, resolving complex bounding queries purely through electrical routing logic.

### AI Alignment & Agent Logic

For organizations grounding AI outputs in deterministic logic, standard interpreters scale poorly. This engine addresses that by fundamentally shifting how complex sets and self-referential structures are processed. Because the system natively evaluates a saturated universe, it can parse queries on the absolute complement space. This allows the construction of **exclusion-first logic gates**, filtering non-matching data paths through a distributed swarm in $O(1)$ time rather than iterating through an $O(N)$ list. Furthermore, geometric bounds checking provides zero-cost loop detection, mathematically restricting the depth of evaluations to guarantee termination without relying on brute-force timeouts. Ultimately, compiling this logic to raw combinators eradicates traditional memory overhead, translating logic into spatial routing instructions primed for massive GPU parallelism.

### High-Energy Physics & Quantum Simulation

In high-energy physics, calculating interactions often assumes an abstract, continuous spacetime—essentially an infinite oracle that provides endless space to resolve equations. This assumption leads to uncomputable mathematical divergences that require artificial hacks (renormalization). Our engine forces these complex interactions to execute within the strict, finite memory arena of a computational graph. 

When evaluating highly entangled states or structural paradoxes, the system demonstrates that forcing classical equivalence triggers **unbounded topological recursion**. Rather than relying on an infinite supply of fresh variable names (like the Specker model) to absorb this friction, the engine must physically track the recursive cascade. It mathematically intercepts this spiral using the **Pigeonhole Principle**: traversing a finite graph more times than there are vertices dictates a mathematically unsolvable negative cycle. By modeling the quantum vacuum as this finitely bounded network, the measurable "energy shift" of a particle is simply the exact algorithmic cost (syntactic friction) required to resolve the logical routing, effectively hardware-simulating quantum interactions without encountering uncomputable infinities.

### Biomolecular Synthesis

Protein folding and biomolecular interactions rely on highly complex, recursive geometric constraints that classical prediction algorithms struggle to bound without exponential computation. By treating molecular structures as causal braids and physical folding tension as topological friction, this engine can natively model biochemical cascades. The internal graph boundaries intercept combinatorial explosions, allowing researchers to predict the physical stability and halflife of newly synthesized molecular knots based directly on the geometric friction required to evaluate their corresponding topological graphs.

---

## Architecture Pipeline

> **Static Verification (Lean 4 Oracle)**  
> The engine replaces dependent type-checking with Bellman-Ford geometric shortest-path routing, mathematically trapping non-terminating logical loops as negative-weight cycles.

> **Combinatory Compiler (AST to S/K/I/U)**  
> Translates the Lean-verified DAG into a flat operational domain. The system algorithmically injects type-shifting T-operators precisely where topological level shifts are required, ensuring strict acyclic stability.

> **High-Performance Backend Transition**  
> The safely bounded combinator strings are optimized for immediate translation into bare-metal CUDA execution via Interaction Nets.

## The Laboratory vs. The Factory

This Lean 4 repository functions as a theoretical laboratory rather than the final operational home for this logic. Building a custom, bare-metal logic engine requires abandoning the safety nets of standard dependent type theory. Consequently, we must first secure cryptographic certainty regarding how Quine's New Foundations operates. By utilizing Lean’s universally trusted kernel to formally prove the exact mechanics of our stratification algorithms, we conduct the rigorous diagnostic work required before forging the actual operational code into a custom engine.

*Note on Computational Limits:* The conversion of formulas into Disjunctive Normal Form (DNF) triggers an exponential combinatorial explosion. This acts as a severe practical bottleneck for Lean's evaluator, restricting the engine to small, targeted canonical paradoxes. However, because the DNF expansion remains structurally recursive and bounded by the finite syntax tree of the input formula, it maintains strict constructivist rigor in alignment with the Intuitionistic Fan Theorem. It guarantees termination and never generates a lawless sequence. Future iterations of the custom logic engine will resolve this bottleneck by integrating CDCL-based SAT evaluation or an SMT solver. Utilizing Integer Difference Logic will evaluate geometric weights dynamically without explicitly expanding memory.

---

## Setup and Building

This repository contains multiple Lean 4 projects. You can execute a fast build by running `lake build` in a project folder, which quickly compiles the core engine and executable. Alternatively, running `lake build NfValidate` performs full verification, compiling the entire library along with all 1000+ line soundness proofs. This takes significantly longer as Lean must mathematically verify every theorem.

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

The program defines a custom inductive type representing first-order logic formulas with a membership relation. A function assigns integer levels to all variables utilizing Bellman-Ford graph evaluation. Equality constraints (`x = y`) encode as bidirectional edges with a weight of 0, while membership constraints (`x ∈ y`) translate into directed edges with a weight of 1.

Stratification functions purely as a grammatical constraint. Coding this validator operationalizes the systematic ambiguity of the language. Classical paradoxes like Russell's paradox do not require semantic interpretation to be resolved; they mathematically manifest as geometric negative weight cycles during the Bellman-Ford traversal.

The repository proves the algorithm's internal monotonicity and convergence, guaranteeing the search map never regresses into cyclic instability. A formalized K-Iteration bound mathematically restricts the depth of type derivations strictly to the number of variables present. This mechanism guarantees termination without unchecked iterative expansion. Ultimately, the `stratification_sound` theorem proves that computational satisfiability in the geometric domain inherently guarantees valid syntax, securing a soundness proof entirely independent of traditional model-theoretic structures.

### `parse-strat`: The Interactive Sandbox

This program provides a tactile, responsive REPL environment for testing edge cases in the constraint solver without compromising the formal proofs of the main diagnostic suite.

A lexical scanner and recursive descent parser allow users to manually inject arbitrary set-theoretic strings (e.g., `~(x = y) & (y e z)`). The algorithm immediately generates the topological graph, detects cycles, and prints the distance maps or exact algebraic telescoping sum contradictions. This sandbox invites researchers to manually test the boundaries of Quine's systemic ambiguity and observe the mechanical reality of the algorithm in real-time.

### `seq-embed`: The Formal Diagnostic Tool

This project formalizes the structural proof theory required to navigate the complexities of the axiom of extensionality. It builds a deep embedding of Gentzen's Sequent Calculus in Lean, restricting comprehension rules strictly to formulas that pass the `nf-validate` stratification checker.

The system mechanically restricts classical deductive freedom. While standard theorem provers invoke comprehension rules whenever a formula is well-formed, this environment mathematically locks the `compL` (Comprehension Left) rule. The logic engine refuses to process a set comprehension unless supplied with a `StratificationWitness` generated by the external Bellman-Ford algorithm.

The diagnostic engine (`reduceCut`) executes canonical failure pathways like the Impredicative Singleton. Rather than building a traditional normalizer to smooth out intermediate lemmas, this engine intentionally bypasses standard structural permutations to force logical detours directly into the `compL` rule.

Marcel Crabbé proved that if a system restricts itself exclusively to strictly stratifiable terms, the set of terms loses closure under substitution. This causes the Hauptsatz (cut-elimination) to fail trivially (Crabbé 1994). By simulating cuts that require substitution across a strictly stratified global graph, the program mechanically surfaces the exact topological contradictions responsible for this grammatical breakdown.

#### Extensionality Collisions vs. Strict Global Stratification

Early versions of this repository operated under **strict global stratification**, mechanically verifying Marcel Crabbé's observation that enforcing rigid global typing destroys structural closure under substitution. 

However, evaluating the true systemic paradoxes of New Foundations requires bypassing these trivial syntactic failures. The engine was upgraded to evaluate **weak stratification**. By partitioning the Bellman-Ford graph according to binding scope, local variables can be typed independently. Once dynamic local re-leveling restores substitution closure, the `reduceCut` diagnostic automatically pushes the resolved cuts upward into the active *Extensionality Axiom*. 

The engine actively demonstrates that it is precisely the structural collision between **dynamic local re-leveling** (weak stratification) and **Extensionality's rigid structural equivalence** ($x = y$) that generates the profound normalization breakdown of NF. When the engine executes this collision, it mathematically proves that classical identity requires an infinite oracle; without one, the equivalence triggers unbounded topological recursion.

### `untyped-comb`: Untyped Combinatory Logic

Standard implementations of the $\lambda$-calculus or combinatory logic in Lean rely heavily on dependent type theory. The `untyped-comb` module constructs an entirely untyped combinatory logic environment and introduces the specific syntactic operators required to make it functional under NF rules. 

By utilizing **Topologically-Guided Lazy Reduction Bounding**, the engine natively compiles operations into a Directed Acyclic Graph (DAG). It leverages Kosaraju's algorithm to flatten semantic cycles and employs Minimum Cycle Mean (MCM) bounds to enforce strict K-Iteration halting limits.

**Dynamic Weight Integration & Automated T-Injection**
Bridging the static validation layer to the execution backend, the engine extracts genuine topological distance bounds (integer constraints) generated by the `NfValidate.StratificationWitness`. The newly integrated **T-Operator Compilation Pipeline** algorithmically reads the AST and automatically synthesizes Thomas Forster's $T$-operator ($x \mapsto \iota"x$) natively into the combinator graph exactly where the distance map indicates a topological level shift. This acts as a geometric stabilizer, ensuring that $S$ and $K$ combinatorial reduction sequences remain completely type-safe through self-regulation without relying on a rigid type-checker or an infinite oracle.

**Categorical Semantics**
The evaluated logic successfully transitions into applied category theory via the **Stratified Pseudo Elephant (SPE)**. This architecture formalizes pseudo-Cartesian closure with $T$-relative adjunctions and processes a self-referential topology. We implemented **Strongly Cantorian Retractions** as dynamic "islands of classicality," where cycle detectors are formally suspended, allowing choice functions and standard arithmetic to execute natively in $O(1)$ time—verified by Knaster-Tarski lattice fixpoints. Through the Strongly Cantorian Universe (SCU) axiom, the engine guarantees fibrewise small maps composition, climaxing in the **Stratified Yoneda Lemma**: $Nat(C(U,-), F) \cong T(F(U))$. The category of NF sets maps its own internal subcategory directly onto the memory arenas, successfully evaluating the Yoneda embedding over the Universal Set $V$ without triggering Extensionality Collisions.

### `CombLib`: Native Operational Semantics

This stable untyped execution environment allows the system to process advanced, paradox-heavy operations natively without memory exhaustion or dependency on external well-ordering axioms:
* **Recursive Self-Models ($V \in V$):** Uses the Y-combinator to evaluate Quine Atoms ($\Omega = \{\Omega\}$), relying safely on the MCM limits to cleanly intercept the self-referential graph.
* **Frege-Russell Numerals:** Defines numbers organically as "the set of all sets of size N," employing node-collision geometries instead of dependent axioms.
* **Choice-Free Cardinal Arithmetic:** Implements Transfinite Calculus (e.g., Cardinal Addition $|A| + |B|$ and $\aleph_0$) entirely via pure $\lambda \to S, K$ bracket abstraction. The system mathematically tracks disjoint union topologies across stratification boundaries, triggering mechanical $T$-functor injections dynamically.
* **Physical Observables & Target Particles:** Explicitly extracts Standard Model empirical metrics (Rest Mass, Coupling Constant, Resonance) directly from measuring the bounded topological recursion cost of structured particle knots (`electron_knot`, `nucleon_braid`).
* **Graph Spectrometer:** Synthesizes geometric properties to compute $m/Q$ mass-to-charge ratios via topological resistance vectors, and outputs algorithmic decay timers mapping recursive engine ticks directly to halflife boundaries.
* **Holographic Data Indexing & Search:** Utilizes the absolute complement ($V \setminus A$) natively permitted by NF to build exclusion-first search algorithms. Target non-matching data is isolated and discarded via an $O(1)$ topological sweep rather than an $O(N)$ iteration. Furthermore, the DAG structure isolates unresolvable contradictions across distributed data swarms in strictly linear time $O(V+E)$.

### ExPrograms: Native Verification

To definitively demonstrate the active architectural integrity of the Stratified Pseudo Elephant, the `ExPrograms` directory hosts executable Lean scripts that organically evaluate these bounds in real-time logic loops:
1. **The Russell Paradox Evaluator:** Proves the MCM halting bounds geometrically limit $R \in R$.
2. **Holographic Data Sieve:** Actively complies and evaluates the absolute complement search.
3. **Native Transfinite Arithmetic:** Synthesizes the $T$-functor mappings natively on unbound operations ($\aleph_0 + \aleph_0$).
4. **The Quine Atom Stabilizer:** Successfully computes pure structural self-models.
5. **Pseudo-Cartesian Closure Test:** Validates stable $T$-shifted evaluation sequences ($ev'_{A,B}$).
6. **Strongly Cantorian Fixpoint Verifier:** Operates and verifies dynamic $\text{lfp}(F)$ limits inside classical islands.
7. **Stratified Yoneda Embedding Test:** Confirms the categorical self-representation natively bounds to $T(F(V))$ without graph collapse.
8. **Discrete Causal Geometry:** Validates Causal Graph Syntactic Monism by measuring algorithmic randomness as structural topological recursion bounds.
9. **Collider Simulation:** Models a particle accelerator by forcing recursive stacks (lazy thunks of structured `electron_knot` primitives), colliding them, and natively resolving the Extensionality contradiction through Resonance magnitude calculation and the Graph Spectrometer, avoiding uncomputable infinities.
10. **Agentic Reflection:** Implements a self-referential autonomous agent operating through sandbox-insulated logic loops, utilizing MCM topological limits for decision-making and SC memory commit.
11. **Agentic Planning:** Expands introspection into an active decision matrix, mechanically simulating divergent topological futures and optimizing choices by routing the path with the lowest required recursion cascade.

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

### Native Systems Execution (The Monist Engine)

We plan to abandon the dependent type constraints of Lean 4 entirely in favor of a bare-metal implementation written in Rust. The verified Topologically-Guided Lazy Reduction Bounds will compile into Arena-Allocated Interaction Nets, optimizing memory traversal for high-performance hardware execution (HVM2/Bend). This transition includes establishing real-time execution bounds via dynamic programming and color-coding heuristics to bypass exhaustive path traversal.

---

## License

This project is licensed under the GNU Affero General Public License v3 (AGPLv3) - see the [LICENSE](LICENSE) file for details.
