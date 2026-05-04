# Parse-Strat: The Interactive ITP Sandbox

This module provides an interactive Read-Eval-Print Loop (REPL) environment acting as a full Interactive Theorem Prover (ITP). It allows users to explore the **weak stratification constraints** of Quine's New Foundations (NF) using classical Natural Deduction tactics while being supported by a powerful topological graph-flattening backend. It serves as the tactile Lean 4 front-end to the core `nf-validate` stratification logic library.

## Purpose and Scope

While the main `seq-embed` diagnostic tool executes hardcoded, canonical proofs, `parse-strat` is designed for organic exploration. It brings LCF-style tactical theorem proving to New Foundations set theory. By blending symbolic rewriting with immediate geometric constraint evaluation, researchers can manually test the boundaries of stratification and observe exactly how dynamic type-raising operations (like the $T$-functor) violently collide with Extensionality bounds.

## Features

* **Lexical Scanner & Parser**: Converts raw user input strings into Abstract Syntax Trees (AST). It supports standard first-order logic operators (`~`, `&`, `v`, `->`, `forall`, `exists`) and set-theoretic relations (`=`, `e`).
* **Tactical Proof State Management**: Defines rigorous `Context` and `Goal` arrays to track logical hypotheses exactly as they unfold in a classical proof.
* **Topological Feedback Engine**: Rather than symbolically rewriting infinite paradoxical regress chains, the REPL can dynamically generate Bellman-Ford constraint graphs of the active logical boundaries, returning explicit integer distance maps (Witness Context) or exact algebraic telescoping sum contradictions.

## Usage

To launch the interactive sandbox, navigate to the `parse-strat` directory and run the executable:

```Bash
lake build
lake exe parse-strat
```

---

## Interactive Tutorial: Proving Strong Cantorian Preservation

The best way to understand the Lean REPL is through a canonical, continuous example. Let's walk through how a user would interactively prove that the Quine pair preserves Strongly Cantorian (SC) sets.

### 1. Defining Axioms

First, we need to declare the foundational rules we are working with using `assume <name> <formula>`.

```text
ITP> assume SC_Def forall x. SC(x) <-> (x = T(x))
Axiom SC_Def added.

ITP> assume Quine_Flatness forall x y. typestate(Q(x,y)) == max(typestate(x), typestate(y))
Axiom Quine_Flatness added.
```
*Note: The system globally registers these named axioms for later retrieval or constraint evaluation.*

### 2. Setting a Goal

We declare the theorem we want to prove using `theorem <name> <formula>`. This transitions the REPL into tactical proof mode.

```text
ITP> theorem SC_Preservation forall a b. (a = Ta /\ b = Tb) -> Qab = TQab
Starting proof of SC_Preservation
```

### 3. Tactical Natural Deduction

We can use `show_goal` at any time to inspect the local Context (hypotheses) and Target. Let's break down the logic using standard Natural Deduction tactics.

```text
ITP> intro a
ITP> intro b
ITP> intro H_SC
ITP> destruct H_SC H1 H2
ITP> show_goal

H1: a = Ta
H2: b = Tb
a: a = a
b: b = b
----------------------
Qab = TQab
```
*The `intro` command brought our variables and implication premise into the context, and `destruct` cleanly split the `H_SC` conjunction into `H1` and `H2`.*

### 4. Rewriting

We use `rewrite <name>` to perform symbolic substitution based on equalities.

```text
ITP> rewrite SC_Def
[Goal Rewritten] Target 1 is now: Qab = TQab

ITP> rewrite H1
ITP> rewrite H2
[Goal Rewritten] Target 1 is now: Q(Ta, Tb) = TQab
```

### 5. Diagnostics and Stratification

At this stage, we might want to hand off the topological heavy lifting to the internal geometric constraint engine. We can use the `eval` command to test if the formula successfully stratifies across the T-boundary!

```text
ITP> eval ((((((a = Ta & b = Tb) & Qab = a) & Qab = b) & QTaTb = Ta) & QTaTb = Tb) & QTaTb = TQab) & Qab = TQab
Stratification successful. Witness: {a@0 : 0, b@0 : 0, Ta@0 : 0, Tb@0 : 0, QTaTb@0 : 0, Qab@0 : 0, TQab@0 : 0}
```
*The `eval` command bypasses the tactical proof state, instantly extracting topological constraints and running the Bellman-Ford cycle detection algorithm to verify mathematical consistency.*

### 6. Managing the Session

You can save your progress mid-proof and load it back later:
```text
ITP> save_session my_proof.json
Session saved to my_proof.json.

ITP> qed
Proof accepted.
```

---

## Unified Command Reference

The Lean `parse-strat` ITP uses a command set strictly unified with the Rust backend interface:

### Core Proof Environment
*   `help`: Show the help message.
*   `exit` / `quit`: Exit the REPL.
*   `save_session <file.json>`: Save the current session (axioms and active goals) to a JSON file.
*   `load_session <file.json>`: Load a previously saved session.

### Axioms & Proofs
*   `assume <name> <formula>`: Register a named axiom into the global environment.
*   `theorem <name> <formula>`: Start a new proof with a target goal and enter tactical mode.
*   `show_goal`: Print the active target goal and its local context/hypotheses.
*   `qed`: Conclude an interactive proof if all goals are solved.
*   `abort`: Cancel the current interactive proof.

### Interactive Tactics
*   `intro [name]`: Introduce a premise or a universally quantified variable into the local context.
*   `exact <name>`: Close the current goal if it exactly matches the specified hypothesis.
*   `apply <name>`: Apply backward reasoning using an implication hypothesis.
*   `split`: Split a conjunction (`&`) goal into two separate sub-goals.
*   `left` / `right`: Choose a side to prove for a disjunction (`v`) goal.
*   `destruct <name> [n1] [n2]`: Break down a hypothesis (like a conjunction or disjunction) into smaller pieces in the context.
*   `rewrite <name>`: Substitute variables inside the goal based on an equality hypothesis.

### Diagnostic Evaluation
*   `eval <formula>`: Immediately test a formula for stratification loops and geometric friction without entering the tactical proof state.
*   `step <formula>`: Process a logical formula step-by-step, providing immediate, color-coded feedback on topological friction and geometric bounds.