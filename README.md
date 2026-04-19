# NF Sketches: Formalizing New Foundations

*A proof-theoretic companion to the [recent NF consistency result](https://github.com/leanprover-community/con-nf) from Lavinia Randall Holmes and Sky Wilshaw.*

Following the landmark formalization of NF's relative consistency by Holmes and Wilshaw, this project extends the Lean 4 ecosystem's coverage of Quine's New Foundations into structural proof theory. While `con-nf` establishes the model-theoretic consistency of the universe, `nf-sketches` provides the exact syntactic and deductive machinery required to operate within it. 

Standard model-theoretic proofs in Lean frequently reproduce the iterative hierarchy, introducing unnecessary friction when modeling a universal set. By bridging the operational mechanics of NF with the precise constraints of the Lean theorem prover, this repository avoids artificial scaffolding. It focuses instead on executing logic organically as a mechanical, grammatical process.

These modules formalize the baseline stratification algorithms and explore the unique behavior of structural rules under Quine's systemic ambiguity. Specifically, the project mechanizes the trivial failure of the Hauptsatz under strict global stratification. By interacting directly with the methodological territory of recent consistency formalizations, this project establishes a rigorous computational baseline that validates structural foundations and operationalizes the core mechanics of syntactic monism.

## The Laboratory vs. The Factory

This Lean 4 repository is not the final home for this logic; it is the theoretical laboratory used to prove the mathematics are sound. Because building a custom, bare-metal logic engine requires abandoning the safety nets of standard dependent type theory, we must first secure cryptographic certainty regarding how Quine's New Foundations operates. By using Lean’s universally trusted kernel to formally prove exactly how our algorithms evaluate stratification, we conduct the rigorous diagnostic work required before forging the actual operational code directly into a custom engine.

*Note on Computational Limits:* The conversion of formulas into Disjunctive Normal Form (DNF) introduces an exponential combinatorial explosion. This acts as a severe practical bottleneck for Lean's evaluator, limiting the engine to small, targeted canonical paradoxes. However, because the DNF expansion is structurally recursive and bounded by the finite syntax tree of the input formula, it maintains strict constructivist rigor (the Intuitionistic Fan Theorem). It never generates a lawless sequence. Future iterations of the custom logic engine plan to resolve this bottleneck by integrating CDCL-based SAT evaluation or an SMT solver (utilizing Integer Difference Logic) to evaluate geometric weights dynamically without explicit memory expansion.

## Core Modules

The repository is divided into three primary modules, separating the core logical constraints from interactive exploration and formal diagnostics.

### `nf-validate`: The Core Stratification Library

This library operates as an algorithmic syntax checker. Instead of proving theorems within NF, the Lean script takes an abstract syntax tree of a logical formula and algorithmically determines its stratifiability. By completely bypassing traditional model theory, this module reduces set theory validation into a purely geometric shortest-path routing problem.

* **Implementation Mechanics:** The program defines a custom inductive type representing the formulas of first-order logic with a membership relation. A function assigns integer levels to all variables using Bellman-Ford graph evaluation. Equality constraints (`x = y`) are encoded as bidirectional edges with a weight of 0, and membership constraints (`x ∈ y`) are translated into edges with a weight of 1.
* **Theoretical Objective:** Stratification functions strictly as a grammatical constraint. Coding this validator operationalizes the systematic ambiguity of the language. Classical paradoxes like Russell's paradox do not require semantic interpretation to be resolved; they mathematically manifest as negative weight cycles during the Bellman-Ford traversal.
* **Formal Verification of Geometric Soundness:** The repository proves the algorithm's internal monotonicity and convergence to guarantee the search map never regresses into cyclic instability. A formalized K-Iteration bound mathematically restricts the depth of type derivations strictly to the number of variables present, guaranteeing termination without unchecked iterative expansion. Ultimately, the `stratification_sound` theorem proves that computational satisfiability in the geometric domain inherently guarantees valid syntax, securing a soundness proof entirely independent of traditional model-theoretic structures.

### `parse-strat`: The Interactive Sandbox

This program provides a tactile, responsive REPL environment for testing edge cases in the constraint solver without compromising the formal proofs of the main diagnostic suite.

* **Implementation Mechanics:** It features a lexical scanner and recursive descent parser that allows users to manually type arbitrary set-theoretic strings (e.g., `~(x = y) & (y e z)`). The algorithm immediately generates the topological graph, detects cycles, and prints the distance maps or exact algebraic telescoping sum contradictions.
* **Theoretical Objective:** This sandbox invites researchers to manually test the boundaries of Quine's systemic ambiguity and observe the mechanical work of the algorithm in real-time.

### `seq-embed`: The Formal Diagnostic Tool

This project formalizes the structural proof theory required to navigate the complexities of the axiom of extensionality. It builds a deep embedding of Gentzen's Sequent Calculus in Lean, restricting the comprehension rules strictly to formulas passing the `nf-validate` stratification checker.

* **Algorithmic Gatekeeping:** The system mechanically restricts classical deductive freedom. While standard theorem provers invoke comprehension rules whenever a formula is well-formed, this environment mathematically locks the `compL` (Comprehension Left) rule. The logic engine refuses to process a set comprehension unless it is supplied with a `StratificationWitness` generated by the external Bellman-Ford algorithm.
* **Sabotaging Normalization:** The diagnostic engine (`reduceCut`) executes canonical failure pathways (such as the Impredicative Singleton). Rather than building a traditional normalizer to smooth out intermediate lemmas, this engine intentionally bypasses standard structural permutations to force logical detours directly into the `compL` rule.
* **Theoretical Objective:** Marcel Crabbé proved that if a system restricts itself exclusively to strictly stratifiable terms, the set of terms loses closure under substitution, causing the Hauptsatz (cut-elimination) to fail trivially (Crabbé 1994). By simulating cuts that require substitution across a strictly stratified global graph, the program mechanically surfaces the exact topological contradictions that cause this grammatical breakdown.

### Extensionality Collisions vs. Strict Global Stratification

Early versions of this repository operated under **strict global stratification**, mechanically verifying Marcel Crabbé's observation that enforcing rigid global typing destroys structural closure under substitution, causing the Hauptsatz (cut-elimination) to fail trivially. 

However, evaluating the true, systemic paradoxes of New Foundations requires bypassing these trivial syntactic failures. The engine was consequently upgraded to evaluate **weak stratification**. By partitioning the Bellman-Ford graph by binding scope, local variables can be typed independently. Once dynamic local re-leveling restores substitution closure, the `reduceCut` diagnostic automatically pushes the resolved cuts upward into the active *Extensionality Axiom*. 

The engine currently demonstrates that it is precisely the violent friction between **dynamic local re-leveling** (weak stratification) and **Extensionality's rigid structural equivalence** ($x = y$) that generates the profound normalization breakdown of NF.

### Future Work: `untyped-comb` (Untyped Combinators)

Standard implementations of the $\lambda$-calculus or combinatory logic in Lean rely heavily on dependent type theory. A future module, `untyped-comb`, is planned to construct an untyped combinatory logic environment and introduce the specific syntactic operators required to make it functional under NF rules. This aims to provide a tangible step toward a Curry-Howard correspondence for stratified set theory.

---

## Field Contributions and Theoretical Context

The deployment of formal mathematical systems as a baseline for metaphysical inquiry represents a crucial interdisciplinary frontier. For decades, the implicit equation of formal ontology with Zermelo-Fraenkel set theory has heavily governed how philosophers and logicians model fundamental structural relationships. Evaluating this theoretical consensus through alternative frameworks introduces vital critical rigor to the philosophy of mathematics.

### Structural Logic and Automated Theorem Proving

The broader mathematical and computer science communities are undergoing a major transition toward formal verification. Engaging deeply with proof theory, type systems, and the Curry-Howard isomorphism builds a profound mechanical literacy regarding the operation of formal systems. Understanding how to manage syntactic constraints, track logical detours in sequent calculus, and resolve type-checking errors translates directly to the development of software verification protocols and the foundational architecture of artificial intelligence.

### Syntactic Monism and Hierarchical Friction

A significant theoretical bottleneck exists in contemporary computational ontology. Standard foundations force a bottom-up construction where objects must be painstakingly assembled stage by stage. Forcing a computational system to model the world through an ascending ladder of types introduces severe friction. Every time a program maps a flat, self-referential physical event into a strictly stratified semantic model, data distorts. 

Monist foundations bypass artificial scaffolding entirely by proposing a universe that contains everything natively. A framework accommodating a universal set allows a logic engine to process the environment as a cohesive whole. In a system like New Foundations, the restriction moves from the objects themselves to the grammar used to describe them. The fundamental computational challenge transforms from building rigid semantic models into enforcing exact syntactic rules. This project explores the operational semantics of recursive functions, the interaction between syntactic constraints and cut-elimination, and the graph-theoretic topology of abstract structures like Wrandalls to map how a universal set sustains its architecture without collapsing into contradiction.

---

## Contrast Against HoTT

Homotopy Type Theory (HoTT) rewrites the foundational rules of mathematics by discarding the static, extensional sets of ZFC in favor of dynamic, intensional spaces. By defining equality as a continuous path between points, HoTT natively captures structural equivalence. The Univalence Axiom formalizes the principle that isomorphic structures are strictly identical, providing a massive computational advantage.

Despite these advancements, HoTT and New Foundations propose radically different solutions to the problem of hierarchical modeling.

### The Persistent Hierarchy of Universes

HoTT successfully escapes the micro-level iterative construction of individual sets. It retains a macro-level hierarchy to maintain systemic stability. To prevent self-referential paradoxes, Martin-Löf type theories require an ascending, infinite tower of universes: `U0​:U1​:U2​…`. Every type must belong to a universe of a higher index. The ontology remains fundamentally layered. When a computational engine attempts to model a heavily entangled physical reality using HoTT, it continually calculates and tracks the specific universe level of every generative event.

### The Syntactic Monist Contrast

New Foundations provides a truly flat alternative. The topology of the NF universe is singular, requiring no ascending tower of domains. It natively accommodates a Universal Set containing everything, including itself. The system averts logical collapse by shifting the burden of consistency entirely away from the ontological structure. The data pool remains an unbounded, saturated whole. The restriction applies strictly to the compiler reading the code, shielding the physical topology from artificial layering.

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

The architectural requirements for formalizing Quine's New Foundations demand a specific convergence of disciplines, establishing the necessary computational baseline to construct the validator and embed the restricted sequent calculus.

* **New Foundations and Stratification:** Quine's originating article (1937) introduces stratification to bypass Russell's Paradox while retaining the universal set. Texts like Forster's *Set Theory with a Universal Set* (1992) and Holmes's *Elementary Set Theory with a Universal Set* (1998) provide the definitive modern diagnostic tools and blueprints for translating abstract stratification rules into programmable logic.
* **Computational Mechanization:** Building an algorithmic syntax checker requires defining logical formulas computationally. Pierce's *Types and Programming Languages* (2002) grounds abstract syntactic concepts in operational semantics, while *Theorem Proving in Lean 4* (Avigad et al. 2023) covers the foundational syntax of the host environment.
* **Structural Proof Theory:** Negri and von Plato's *Structural Proof Theory* (2001) provides a rigorous breakdown of Gentzen’s Sequent Calculus. Crabbé's diagnostic paper on the consistency of NF's impredicative subsystem (1982) outlines the mechanics of cut-elimination within stratified comprehension, exposing the tension where eliminating cuts can accidentally yield illegal syntax.
* **Algorithmic Verification:** Treating variables as vertices and membership relations as directed edges transforms stratification into a topological problem. Standard discrete mathematics and graph theory texts supply the rigorous definitions for directed acyclic graphs and pathfinding algorithms required to verify valid level assignments programmatically.

---

## Research Applications and Next Steps

This repository serves as a computationally rigorous baseline for exploring the mechanical limits of formal logic under Quine's systemic ambiguity. By providing both interactive REPL sandboxes and automated cut-elimination diagnostics, the tools enable researchers to mathematically witness the exact boundaries of a stratified universe.

These modules provide the verified infrastructure necessary to further investigate the computational potential of New Foundations, laying the groundwork for future implementations of untyped combinatory logic and custom, non-hierarchical logic engines.