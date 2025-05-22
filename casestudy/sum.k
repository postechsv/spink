requires "../promela.k"
requires "domains.md"

module SPEC-SYNTAX
  imports PROMELA-SYNTAX
endmodule

module VERIFICATION
  imports K-EQUAL
  imports SPEC-SYNTAX
  imports PROMELA
  imports MAP-SYMBOLIC
endmodule

module SUM
  imports VERIFICATION

  syntax Id ::= "$n" [token] | "$s" [token]

  claim [summation]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: 0 < $n ; $s = $s + $n ; $n = $n - 1
                :: 0 >= $n ; break
              od
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(I0:Int))
              (lval($n,0) |-> loc(I1:Int))
            </env>
       ...</proc>
        </procs>

        <store>
          (I0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (I1 |-> (N:Int => 0))
        </store>

        <lock> #none </lock>
    requires N >Int 0 
endmodule 
