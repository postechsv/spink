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

module HCHAN
  imports VERIFICATION

  syntax Id ::= "$x" [token] | "$y" [token]

  /*claim [handshake]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> $x[0] ! 42 => .K </k>
            <env>
              (lval($x,0) |-> hs(C))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k> $x[0] ? $y => .K </k>
            <env>
              (lval($y,0) |-> loc(L))
              (lval($x,0) |-> hs(C))
            </env>
       ...</proc>
        </procs>
        <store>
          (L |-> (_ => 42))
        </store>
        <lock> #none </lock>*/

  claim [handshake-chain]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> atomic { $x[0] ! 42 ; $y[1] = ($y[1] * 10) + 1 } => .K </k>
            <env>
              (lval($y,0) |-> loc(0))
              (lval($y,1) |-> loc(1))
              (lval($x,0) |-> hs(0))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k> atomic { $x[0] ? $y[0] ; $x[1] ! 42 ; $y[1] = ($y[1] * 10) + 2 } => .K </k>
            <env>
              (lval($y,0) |-> loc(0))
              (lval($y,1) |-> loc(1))
              (lval($x,0) |-> hs(0))
              (lval($x,1) |-> hs(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 3 </pid>
            <k> atomic { $x[1] ? $y[0] ; $y[1] = ($y[1] * 10) + 3 } => .K </k>
            <env>
              (lval($y,0) |-> loc(0))
              (lval($y,1) |-> loc(1))
              (lval($x,1) |-> hs(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 4 </pid>
            <k> ($y[1] = ($y[1] * 10) + 4):Stmt => .K </k>
            <env>
              (lval($y,0) |-> loc(0))
              (lval($y,1) |-> loc(1))
            </env>
       ...</proc>
        </procs>
        <store>
          (0 |-> (0 => 42))
          (1 |-> (0 => ?I:Int))
        </store>
        <lock> 1 => ?_ </lock>
     ensures ?I ==K 4321 orBool ?I ==K 3214

 /* claim [toss]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> (#toss(3) ~> #rel) => .K </k>
      ...</proc>
        </procs>
        <lock> 1 => 3 </lock> // the loose rule may release this
*/
endmodule 
