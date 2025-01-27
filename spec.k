requires "promela.k"
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

module SPEC
  imports VERIFICATION

  syntax Id ::= "$a" [token] | "$b" [token] | "$c" [token]

  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              ($a [ 0 + run $b ( .Exprs ) ] = (40 + run $b ( .Exprs ))):Stmt
              => .K </k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <lock> #none </lock>
        <store> 0 |-> 42 </store>
        <nextPid> 1 </nextPid>

/*
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              if
                :: if
                     :: $a [ 0 ] = 2 ; $a [ 0 ] = 42  // true branch
                     :: $a [ 0 ] = 3 ; $a [ 0 ] = 100 // false branch
                   fi //; $a = 500
                :: $a > 1 ; $a [ 0 ] = 42  // true branch
              fi
             => .K </k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <lock> 0 </lock>
        <store> 0 |-> -1 </store>
*/
endmodule
