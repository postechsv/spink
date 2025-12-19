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

### Deductive Verification

## Part II: K Framework
- why K
- short tutorial

## Part III: Challenge
- Promela codes

## Part IV:Solution
- Load-and-Fire

## Part V: Concrete Examples
- Sec 4,5 main

## Part VI: Case Study