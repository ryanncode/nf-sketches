# Seq-Embed: Deep Embedding of Stratified Sequent Calculus

This project provides a formal deductive environment in Lean 4 for navigating the structural proof theory of Quine's New Foundations (NF). By deeply embedding Gentzen's Sequent Calculus, the system creates an isolated computational arena that restricts set comprehension exclusively to well-stratified formulas.

## Core Objective

Rather than functioning as a generalized, interactive theorem prover, this module acts as a highly specialized, automated diagnostic tool. The primary objective is to execute logic organically as a mechanical process and observe the exact mathematical breakdown of proof normalization under Quine's systemic ambiguity.

Marcel Crabbé proved that cut-elimination holds for predicative fragments of NF but fails explicitly when cuts interact with stratified comprehension. This codebase operationalizes that failure, acting as a direct, automated witness to the structural limits of a stratified universe.

## Architecture and Execution

The repository features a complete, formally verified execution pipeline that triggers theoretical errors mathematically.

* **Isolated Deductive System:** The calculus is modeled as an explicit inductive family of types (`Derivation`). This prevents Lean's native classical metalogic from interfering with the specific constraints of the object language.
* **Restricted Comprehension (`compL`):** Set comprehension is strictly gated. A derivation step requires a mathematical proof that the underlying formula successfully passes the Bellman-Ford cycle detection algorithm exported from the `nf-validate` library.
* **Targeted Cut Reduction:** The `reduceCut` engine is programmed to handle principal reductions and targeted structural permutations to successfully transport a cut formula into the comprehension diagnostic, bypassing non-essential permutative pathways.
* **Automated Batch Processing:** The `main` executable bypasses manual REPL interaction to automatically run hardcoded, canonical derivation trees. It immediately passes these trees into the normalization engine to trigger the paradoxes.

## Canonical Failure Diagnostics

When the executable runs, it processes five canonical test cases. Each case is designed to force a specific logical variable to occupy two different, contradictory "type levels" simultaneously. The engine surfaces the resulting negative-weight cycles, which represent the mathematical collapse of syntactic stratification:

1. **The Identity Collapse:** Demonstrates the simplest failure of type-level assignment. The system attempts to define a set $A$ whose members are exactly the element $z$, governed by the comprehension formula $∀ y(y ∈ A ↔ y = z)$. Stratification requires $A$ to be one level higher than $z$. The diagnostic then forces a logical cut asserting that $z$ and $A$ are identical ($z = A$), immediately collapsing the required level difference and triggering a cycle.
2. **The Impredicative Singleton:** Models a variation of Russell's paradox. It defines a set $S$ containing elements that do not contain a specific variable $w$, governed by the comprehension formula $∀ x(x ∈ S ↔ x ∉ w)$. The diagnostic forces the substitution $w = S$. The initial formula remains stratifiable, but the engine catches the breakdown at the exact moment of instantiation, proving that the paradox lies in the self-referential application of the rule.
3. **The Transitive Membership Collapse:** Forces a multi-tiered cycle to test the depth of the graph evaluator. It defines a chain of membership: elements of $A$ are members of $B$, which is a member of $C$, governed by the comprehension formula $∃ A ∀ y(y ∈ A ↔ y ∈ B ∧ B ∈ C)$. This requires $C$ to be two levels higher than $A$. The diagnostic cuts this against the assertion that $A = C$, proving the engine can detect contradictions across expanded distance intervals.
4. **The Russell-Prawitz Normalization Breakdown:** Mechanically translates the proof-theoretic infinite regress of the classic Russell set ($R = \{x | x ∉ x\}$) into a geometric self-loop. By attempting to normalize the unstratified set against itself, the engine computationally proves that the Bellman-Ford algorithm successfully halts the infinite regress by detecting the unstratifiable self-reference.
5. **The Kuratowski Ordered Pair Type-Shift:** Captures the multi-level type deviation intrinsic to standard set theory. In the Kuratowski definition, an ordered pair $P$ must be strictly two levels higher than its foundational elements. The diagnostic asserts that $P$ is identical to one of its own foundational elements ($P = A$), forcing an unstratifiable collapse across multiple hierarchical boundaries.

## Usage

To run the automated diagnostic tool and view the mathematical trace outputs:

```Bash
lake build
lake exe seq-embed
```