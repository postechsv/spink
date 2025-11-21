# SpinK: A Formal Executable Semantics of PROMELA in K
<img src="./spink.png", height="100px", width="100px">

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
krun example/test_1.pml -d promela-kompiled // generates promela-kompiled/(test_id)_coverage.txt
...
krun example/test_n.pml -d promela-kompiled // generates promela-kompiled/(test_id)_coverage.txt
python3 coverage.py // aggregates all promela-kompiled/*_coverage.txt and generates coverage.xml
cat coverage.xml
```
