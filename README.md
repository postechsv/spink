# SpinK: A Formal Executable Semantics of PROMELA in K
<img src="./spink.png", height="100px", width="100px">

This repository contains semantic definitions of PROMELA using K-Framework,
along with other resources
(e.g., testcases, deductive verification examples, etc.)
appeared in our paper at [VMCAI 2026](/#).

## kompile
```
kompile promela.k --backend haskell
```

## krun
```
krun example/code.pml
krun example/code.pml -d promela-kompiled --search
```

## kprove
```
kprove spec.k
kprove casestudy/spec.k --verbose
```

## coverage
```
pip3 install kframework
kompile promela.k --backend llvm --coverage // currently, haskell is not supported for coverage
// krun example/test_1.pml -d promela-kompiled // generates promela-kompiled/(test_id)_coverage.txt
// ...
//krun example/test_n.pml -d promela-kompiled // generates promela-kompiled/(test_id)_coverage.txt
for f in examples/*.pml; do echo "=== running $f ==="; krun -d promela-kompiled "$f"; done
python3 coverage.py // aggregates all promela-kompiled/*_coverage.txt and generates coverage.xml
cat coverage.xml
```

# Artifact
The main purpose of this artifact is to provide
our case study examples
(`casestudy/`) covered in Section 6 of our paper.
We additionally provide semantics definition
(`promela.k`) of PROMELA in K,
along with some examples
(`examples/`) for validation.

## Getting Started

### Directory Structure
The following shows the directory structure of our artifact:
```
spink/
├─ spin651_linux64   # A spin executable (accessed by the alias 'spin')
├─ casestudy/        # Case study examples from the paper
├─ examples/         # Some running PROMELA examples 
└─ promela.k         # PROMELA semantics definition in K
```
To reproduce our case study,
follow the three steps described below.
For the shell commands below, we assume the user is running
under `spink/` in the container.

### Step 2 - Compile the Semantics Definition
To obtain a deductive verifier (`kprove`)
and an interpreter (`krun`) from our K-semantics,
compile the semantics definition
(`artifact/spink/promela.k`) with the following command:
```
kompile promela.k --backend haskell
```
If successful, no output will be produced.

### Step 3 - Case Study
In our paper (Section 6), we demonstrated two case studies of proving reachability claims for PROMELA programs.
Below we provide commands to reproduce the result of using the K deductive prover `kprove` against our two examples: `Summation` and `Bakery`.
We used a laptop machine (i5-1335U 2.50 GHz / 16 GB RAM) for this experiment.

#### (1) Summation (`casestudy/sum.k`)
Running the following command will output `#Top`,
indicating that the spec has been successfully proved.
This took approximately 10 seconds in our machine.
```bash
kprove casestudy/sum.k
```
#### (2) Bakery (`casestudy/bakery-2procs.k`)
Running the following command will output `#Top`.
This took approximately 5 minutes in our machine.
```bash
kprove casestudy/bakery-2procs.k
```

## Additional Examples
For reference, we additionally provide some PROMELA programs under
`spink/examples`, which can be executed via `krun`.
One can (manually) compare the execution behavior between `krun` and `spin`, which is how we tested our semantics during the semantics design phase.

### Testing PROMELA models in `examples/`
There are two types of examples in `examples/`:
* `examples/example.pml` (ends with `.pml`)
* `examples/example.k` (ends with `.k`)

For the first type, one can execute the model directly 
via `krun`:
```bash
krun examples/example.pml
```
NOTE: most of the examples for this type will be terminated within a few seconds.
An exception:
`examples/spin-peterson` took about 3 minutes in our experiment.

For the second type (for `goto`), one can check the execution behavior via `kprove`:
```bash
kprove examples/example.k
```
NOTE: for the example `examples/paper-atomic-goto2.k`, `kprove` will raise an error.
This is intended.

Some examples are related to the motivating examples
mentioned in our paper:
* `if3.pml`: nested options (Section 4)
* `paper-interference.pml`: 
cross-process interference by handshake 
under nondeterminism (Section 4)
* `paper-atomic-goto1.k`: 
goto under atomicity (Section 5)
* `paper-atomic-goto2.k`: 
goto under atomicity (Section 5)
* `paper-spin-atomic-handshake.pml`: 
handshake under atomicity (Section 5)
* `paper-sum.pml`:
summation model (Section 6)

Some (variants of) examples from SPIN repository
(e.g. official document, github repository, etc.)
are annotated with the keyword `spin` in their file names.

Brief explanations are given as comments.

### Demo
As an example, the following is a PROMELA model 
that sequentially assigns 
`1` and then `2` to a global variable `x`.
(NOTE: in PROMELA, `x` is syntactic sugar for `x[0]`. 
Our examples use the desugard version most of the time)

```promela
// file: examples/assign1.pml
int x[1] = 0

active proctype p() {
  x[0] = 1 ; x[0] = 2
}
```

#### Executing via `spin` 
Run the following command:
```bash
spin -p -g -l -w examples/assign1.pml
```

This will output the trace as follows:
```
  0:    proc  - (:root:) creates proc  0 (p)
  1:    proc  0 (p:1) examples/assign1.pml:4 (state 1)  [x[0] = 1]
                x[0] = 1
  2:    proc  0 (p:1) examples/assign1.pml:4 (state 2)  [x[0] = 2]
                x[0] = 2
  2:    proc  0 (p:1)       terminates
1 process created
```

Here, `x[0] = 1` and `x[0] = 2` 
(not surrounded by square brackets) 
describe how the states are mutated over time.
We remark that in general, when the PROMELA program is nondeterministic, the output may give different results
on each run of `spin`.

#### Executing via `krun`
Run the following command:
```bash
krun examples/assign1.pml
```

This will output the **final K configuration** as follows:
```
// only core parts are shown for simplicity
<T>
  <procs>
    <proc>
      <pid> 0 </pid>
      <name> p </name>
      <k> .K </k> // <--- indicates p has terminated
      <env> lval ( x , 0 ) |-> loc ( 0 ) </env>
    </proc> 
    <proc>
      <pid> -1 </pid>
    </proc>
  </procs>
  <store> 0 |-> 2 </store>
  <network> .Map </network>
  <lock> #none </lock>
</T>
```

Here, the environment cell (`<env>`)
for the process `p` binds the (array) variable `x[0]`
to the location `0` at the store cell (`<store>`),
having the value `2`.
This corresponds to the final log `x[0] = 2`
from the `spin` execution result.
We remark that when the program is nondeterministic,
all possible K-configurations are shown,
separated by `#or`.

## Notations
We list some notational differences between
our artifact (left) and our paper (right).
* `lval(X,I)` <-> `X[I]` (in the environment)
* `<store>` <-> `str`
* `<network>` <-> `net`
* `<local>` <-> `lVars`
* `mq` <-> `q` (message queue)
* `ch(N)` <-> `bch(N)`
* `hs(N)` <-> `hch(N)`
* `#none` <-> `\bot` (global lock)
* `SetItem(@[K1])...SetItem(@[Kn])` <-> `[K1|...|Kn]`
(multiset lifted continuation)

