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

  // loop invariant
  claim <procs>
          <proc>
            <k>
              do
                :: $a < 3 ; $a = $a + 1
                :: $a >= 3 ; break
              od
             => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> (0 => ?I:Int) </store>
    ensures ?I <=Int 3


/*  // select
  claim <procs>
          <proc>
            <k>
              if
                :: $a > 1 ; $a = 42  // true branch
                :: $a > 2 ; $a = 42  // true branch
                :: $a > 3 ; $a = 100 // false branch
              fi
             => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> (3 => 42) </store>
*/

/* // assign
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
*/


/* // choice for epxr
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
