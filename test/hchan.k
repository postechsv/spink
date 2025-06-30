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

  claim [handshake]:
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
        <lock> #none </lock>

endmodule 
