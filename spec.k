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
  syntax Id ::= "$n" [token] | "$s" [token]
              | "$p" [token] | "$L" [token] 

  claim <procs>
          <proc>
            <pid> 1 </pid>
            <name> $p </name>
            <k>
              do
                :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
                :: 0 >= $n ; goto $L
              od
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(0))
              (lval($n,0) |-> loc(1))
            </env>
          </proc>
        </procs>

        <proctypes>
          <proctype>
            <procName> $p </procName>
            <procParams> .Decls </procParams>
            <procBody> skip </procBody>
            <gotoMap> $L |-> choice(false, .K) </gotoMap>
          </proctype>
        </proctypes>

        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
    requires N >Int 0 
endmodule
