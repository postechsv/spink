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

module PAPER-ATOMIC-GOTO2
  imports VERIFICATION

  syntax Id ::= "$p" [token] | "$x" [token]
              | "$y" [token] | "$l" [token]

/*
active proctype p1() {
  atomic { true ; goto L ; true }; // jump out of atomic block
  L: x = x + 1;
  x = x + 1
}

active proctype p2() {
  y = x
}
*/

  claim [goto]:
        <proctype>...
          <procName> $p </procName> 
          <gotoMap>...
            $l |-> gotoCtx(false,
              SetItem(@[ $x[0] = $x[0] + 1 ~> #rel ]) ~> $x[0] = $x[0] + 1)
              // this is loaded continuation of $x[0] = $x[0] + 1 ; $x[0] = $x[0] + 1 under atomicity
       ...</gotoMap>
     ...</proctype>
        <procs>
          <proc>... <pid> -1 </pid> <k> .K => ?_ </k> ...</proc>
          <proc>...
            <pid> 1 </pid> <name> $p </name>
            <k>
              atomic { true ; goto $l ; true }; // $l starts from here!
              $x[0] = $x[0] + 1;
              $x[0] = $x[0] + 1
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k>
              $y[0] = $x[0] => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (0 => ?_))
          (1 |-> (0 => ?Y:Int))
        </store>

        <lock> #none </lock>
        <active> ListItem(1) ListItem(2) => ?_ </active>
  ensures ?Y =/=K 1 // this should raise ERROR because atomicity is lost due to goto


endmodule
