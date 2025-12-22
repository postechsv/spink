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
### PROMELA in K
- PROMELA supports **high-level** **modeling** features for **control-flow**, **concurrency** and **nondeterminism**.
- PROMELA supports **high-level** **modeling** features with interplay between **concurrency** and **nondeterminism** that looks **imperative**.
- When these features are combined, it poses **challenges** for defining formal semantics in K:
    - granularity : **high-level** features
    - nested guards : **declarative** control-flow
    - interference : synchronization under **concurrency** and **nondeterminism**
- Goal: A K semantics that resolves these challenges in an **uniform** and **modular** way (non-ad-hoc way).

### Challenge 1: Basic Statements are not so Basic!
- Example: c ? x, y
    - basic statement -> ATOMIC operation
    - behavior: check, dequeue, assign x, assign y
- How to define K rules for this?
    - A single K rule would work..
    - but harms readability and modularity (c.f., assignment)
- What if..
    - separate K rules for check, dequeue, assign
    - p: check, q: check, p: dequeue
    - q: check becomes invalid!
```
active proctype p() {
    ...
    c ? x, y;
    ...
}
active proctype q() {
    ...
    c ? x, y;
    ...
}
```
- **Granularity mismatch between PROMELA statements and K rules!**


### Challenge 2: Nested Guards
- guards has no imperative interpretation
- guards are **declarative** in nature
```
active proctype p() {
  if
    :: A
    :: do :: B :: C od ; D
}
```

### Challenge 3: Nondeterminism may Interfere across Processes
- Inner concurrency vs Outer concurrency
```
active proctype p1() {
  if :: c ! 1 :: y = 1 fi 
}
active proctype p2() {
  if :: y = 1 :: c ? x fi 
}
```

## Semantic Patterns
### Fire-and-Release
### Load-and-Fire

## Part V: Concrete Examples
- Sec 4,5 main

## Part VI: Case Study
### All-Path Reachability Logic

### Bakery Algorithm