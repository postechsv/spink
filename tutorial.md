# SpinK Tutorial

## Part I: Introduction

### PROMELA
- PROMELA is the input language for SPIN model checker.
    - ACM Software System Award 2001 (cite)
- PROMELA & SPIN tandem is widely used for specifying & verifying concurrent systems.
    - e.g., cryptographic protocols (cite), LINUX FUTEX (cite), Flight Guidence Systems (cite)
- PROMELA has a imperative-style syntax, similar to C:
    - e.g., variable assignment, goto statements, control structures (if, do, etc.)
```
    int x;
    x = 5;
    if
    :: x > 0 -> x = x - 1;
    :: else -> goto end;
    fi;
end:
```
- However PROMELA is a high-level **modeling language**, unlike C.
    - It abstracts away low-level implementation details.
    - e.g., atomic, message-passing
```
    atomic {
        x = x + 1;
        y = y + 1;
    }
```

### Limitation of SPIN
- The SPIN model checker takes PROMELA code as input and performs **automatic** verification.
- SPIN supports highly efficient verification techniques:
    - Partial-order reduction
    - Bitstate hashing
- However, SPIN is based on **explicit state exploration**
    - It cannot verify properties that require reasoning about infinite state spaces or infinite data.
    - Other verification techniques (e.g., deductive verification) are not directly supported.

### Deductive Verification of PROMELA
- Deductive verification is a complementary approach to model checking.
    - It uses logical reasoning to prove properties about programs.
- Deductive verification can handle infinite state spaces and data.
- However, applying deductive verification to PROMELA is challenging:
    - PROMELA's semantics are complex and not formally defined in a way that supports deductive reasoning.
    - Existing tools for deductive verification do not support PROMELA directly.
- To address this, we propose using the K Framework to define formal semantics for PROMELA.

## Part II: K Framework
### K Framework
- A Language Agnostic Framework for Formal Semantics (rosu)
- Many success stories:
    - e.g. C, Java, JavaScript, Ethereum etc.
- K semantics can be used to automatically generate tools for:
    - e.g., parsers, interpreters, model checkers, symbolic execution engines, etc.
    - from a single semantic definition.
    - (add diagram)
- Our approach:
    - Define formal semantics for PROMELA in K.
    - Obtain a deductive verifier for PROMELA **for free**.

### K Semantics
- K is based on rewriting logic.
    - A program's state is represented as a configuration (a K cell).
    - A transition system is defined using rewrite rules (K rules) between two configurations.
- compuations are explicit **data**, modeled as **K continuations**.
    - example of K continuations
- example configuration for IMP
- example rewrite rules for IMP
    - assignment, lookup, etc

### Operational Semantics in K
- example rule: assignment
    - (show rule side-by-side with mathematical notation and xml-like syntax)
- example trace: assignment
    - (show example trace of a simple PROMELA program)
- remark
    - concurrency: via nondeterministic application of rules
    - modularity: easy to extend the lanugage with new constructs (e.g., output cell)
    - executability: via step-by-step applying rules from initial configuration


## Part III: Defining PROMELA Semantics in K
### Semantics of PROMELA
- A PROMELA program models a system of concurrent processes
    - each process's behavior is given by a sequence of statements
- Two levels of Statements
    - basic statements: defines atomic actions
        - e.g.,assignment, channel send/receive, etc.
    - control statements: determines which action comes after another (control-flow)
        - e.g., if, do, etc.
- Enabledness (= Executability)
- An execution of a PROMELA program is a sequence of basic statements
    - (example code: producer-consumer)

### PROMELA in K
- PROMELA supports **high-level** **modeling** features for **control-flow**, **concurrency** and **nondeterminism**.
- PROMELA supports **high-level** **modeling** features with interplay between **concurrency** and **nondeterminism** that looks **imperative**.
- When these features are combined, it poses **challenges** for defining formal semantics in K:
    - granularity : **high-level** features
    - nested guards : **declarative** control-flow
    - interference : synchronization under **concurrency** and **nondeterminism**
- Goal: A K semantics that resolves these challenges in an **uniform** and **modular** way (non-ad-hoc way).

### Challenge 1: "Not-So-Basic" Basic Statements
- Example: receive from a buffered channel
    - a PROMELA basic statement (an **atomic** operation)
    - behavior: check, dequeue, assign x, assign y (not so basic :()
```
active proctype p1() {
    ...
    c ? x, y; // <- currently executing
    ...
}
active proctype p2() {
    ...
    c ? x, y; // <- currently executing
    ...
}
```
- **Granularity mismatch between PROMELA statements and K rules!**
    - PROMELA : 1 intended step
    - K : 4 natural steps
- Designing a single giant K rule for c ? x, y would do, but..
    - harms modularity (e.g., duplicate functionality with assignment rules)
- concurrency matters
    - an interleaving : check (p1) -> check (p2) -> dequeue (p1) -> ...
    - check (p2) becomes invalid!


### Challenge 2: "Schrödinger's" Guards
- Example code: nested nondeterminism
```
// usual style
active proctype p() {
  if
    :: x == 1 -> ...
    :: x > 42 -> ...
  fi
}
```
```
// nested style
active proctype p() {
  if
    :: A
    :: do :: B :: C od // the whole do loop is a guard!
  if ; D
}
```
- A naive "structural" K rules (i.e., branch step-by-step) won't work:
    - **syntactically**, `if` comes before `do`
    - **semantically**, `do` comes before `if` (`if`'s enabledness depends on `do`'s enabledness) 
- How?
    - try recursively and rollback in case of failure? (demonic)
    - choose anything and invalidate the whole execution in case of failure? (angelic)
- **Syntax-Semantics mismatch for nondeterminism**
- Analogy: Given multiple Schrödinger's boxes, choose all and only those boxes with alive cats
    - box <-> nested syntax
    - opening a box <-> commiting to a branch
    - alive cat <-> enabled branch

### Challenge 3: "Entangled" Nondeterminism
- Example code: cross-process interference
    - when p1 chooses the first, p2 is forced to choose the second (handshake should occur)
    - when p1 chooses the second, p2 is forced to choose the first (handshake cannot occur)
```
active proctype p1() {
  if :: c ! 1 :: y = 1 fi 
}
active proctype p2() {
  if :: y = 1 :: c ? x fi 
}
```
- p1's enabledness depends on p2's enabledness and vice versa (circular dependency)
    - enabledness condition cannot be expressed as a pure expression over global program state
    - standard way to check handshake enabledness: pattern matching for two partner processes
```
<k> if (:: c ! v) OS:OptionSet fi ~> K </k>
<k> if (:: c ? x) OS':OptionSet fi ~> K' </k>
```
- handshake operations may be nested at unbounded depth
    - this corresponds to infinite instances of handshake rules for each nesting depth
```
<k> if (:: if (:: ... if (:: c ! v) OS_1_1 fi) OS_1_2 fi) OS_1_N fi ~> K </k>
<k> if (:: if (:: ... if (:: c ? x) OS_2_1 fi) OS_2_2 fi) OS_2_M fi ~> K </k>
```
- challenge: ****


## Semantic Patterns
### Approach

### Fire-and-Release

### Load-and-Fire
- a set of structural rules that transforms a **syntactically nested control-flow** into a **flat semantic multiset**
- Two sources of nondeterminism:
    - branching nondeterminism: `if` in each process
    - interleaving nondeterminism: interleaving between processes

### Forked Continuations

### Modularity

## Part V: Concrete Examples
- Sec 4,5 main

## Part VI: Case Study
### All-Path Reachability Logic

### Bakery Algorithm