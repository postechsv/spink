requires "minimela.k"
requires "domains.md"

module SPEC-SYNTAX
  imports MINIMELA-SYNTAX
endmodule

module VERIFICATION
  imports K-EQUAL
  imports SPEC-SYNTAX
  imports MINIMELA
  imports MAP-SYMBOLIC
endmodule

module SPEC
  imports VERIFICATION

  syntax Id ::= "$x" [token] | "$n" [token] | "$s" [token]

  claim [summation]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
                :: 0 >= $n ; break
              od
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(0))
              (lval($n,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
    requires N >Int 0 

  claim [assign]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> ($x = 42):Stmt => .K </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (_ => 42))
        </store>
endmodule 
