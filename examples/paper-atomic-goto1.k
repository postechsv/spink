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

module PAPER-ATOMIC-GOTO1
  imports VERIFICATION

  syntax Id ::= "$p" [token] | "$x" [token]
              | "$y" [token] | "$l" [token]
//| "$p1" [token]

/*
active proctype p1() {
  goto L; x = 2
  atomic {
    x = x + 1;
L:  x = x + 1; // jump into atomic block
    x = x + 1
  }
}

active proctype p2() {
  y = x
}
*/

  claim [goto]:
        <proctype>...
          <procName> $p </procName> 
          <gotoMap>...
            $l |-> gotoCtx(true,
              SetItem(@[ $x[0] = $x[0] + 1 ~> $x[0] = $x[0] + 1 ~> #rel ]))
              // this is the loaded continuation of $x[0] = $x[0] + 1 ~> $x[0] = $x[0] + 1 ~> #rel under continuity
       ...</gotoMap>
     ...</proctype>
        <procs>
          <proc>... <pid> -1 </pid> <k> .K => ?_ </k> ...</proc>
          <proc>...
            <pid> 1 </pid> <name> $p </name>
            <k>
              goto $l;
              $x[0] = 2;
              atomic {
                $x[0] = $x[0] + 1; // $l starts from here!
                $x[0] = $x[0] + 1;
                $x[0] = $x[0] + 1
              } => .K
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
  ensures ?Y =/=K 1


endmodule
