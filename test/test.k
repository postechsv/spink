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

module TEST 
  imports VERIFICATION

  syntax Id ::= "$x" [token] | "$y" [token]

  claim [assign]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> ($x = 42):Stmt => .K </k>
            <env>
              (lval($x,0) |-> loc(L:Int))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>

        <store>
          (L |-> (_ => 42))
        </store>


  claim [send]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> $x[0] ! 42 => .K </k>
            <env>
              (lval($x,0) |-> ch(C))
            </env>
       ...</proc>
        </procs>
        <network>
          (C |-> mq(10, .List => ListItem(m(ListItem(42)))))
        </network>
        <lock> #none </lock>

  claim [recv-ok]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> $x[0] ? $y => .K </k>
            <env>
              (lval($y,0) |-> loc(L))
              (lval($x,0) |-> ch(C))
            </env>
       ...</proc>
        </procs>
        <store>
          (L |-> (_ => 42))
        </store>
        <network>
          (C |-> mq(10, ListItem(m(ListItem(42))) => .List))
        </network>
        <lock> #none </lock>

  claim [recv-match]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> $x[0] ? 42 => .K </k>
            <env>
              (lval($x,0) |-> ch(C))
            </env>
       ...</proc>
        </procs>
        <network>
          (C |-> mq(10, ListItem(m(ListItem(42))) => .List))
        </network>
        <lock> #none </lock>

  claim [sendrecv]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> $x[0] ! 42 => .K </k>
            <env>
              (lval($x,0) |-> ch(C))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k> $x[0] ? $y => .K </k>
            <env>
              (lval($y,0) |-> loc(L))
              (lval($x,0) |-> ch(C))
            </env>
       ...</proc>
        </procs>
        <store>
          (L |-> (_ => 42))
        </store>
        <network>
          (C |-> mq(SIZE, .List))
        </network>
        <lock> #none </lock>
  requires SIZE >Int 0

endmodule 
