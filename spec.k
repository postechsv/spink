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
              if
                :: if
                     :: $a > 2 ; $a = 42  // true branch
                     :: $a > 3 ; $a = 100 // false branch
                   fi //; $a = 500
                :: $a > 1 ; $a = 42  // true branch
              fi
             => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <lock> 0 </lock>
        <store> 0 |-> 3 </store>

endmodule
