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

  syntax Id ::= "$a" [token]

  claim <procs>
          <proc>
            <k> (
              SetItem(choice(sil, ($a = 1):Stmt))
              SetItem(choice(sil, $a == 2))
              SetItem(choice(sil, $a == 3))
            ) => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> (42 => 1) </store>




/*
  claim <procs>
          <proc>
            <k> (
              SetItem(choice(sil, $a == 1))
              SetItem(choice(sil, $a == 2))
              SetItem(choice(sil, $a == 3))
            ) => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> 2 </store>
*/


endmodule
