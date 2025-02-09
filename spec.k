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
              goto $L ; $s[0] = 40
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
            <gotoMap> $L |-> choice(false, ($s[0] = 41):Stmt ~> .K) </gotoMap>
          </proctype>
        </proctypes>

        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
 

/* TODO loop inv
  claim <procs>
          <proc>
            <pid> 1 </pid>
            <k>
                do
                  :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
                  :: 0 >= $n ; break
                od
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(0))
              (lval($n,0) |-> loc(1))
            </env>
          </proc>
        </procs>
        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
    requires N >=Int 0
*/

/*
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              $c [ 0 ] ? $a [ 0 ]
              => .K
            </k>
            <env>
              (lval($a,0) |-> loc(0))
              (lval($c,0) |-> bfPort(0))
            </env>
          </proc>
        </procs>
        <lock> #none </lock>
        <store> 0 |-> 0 </store>
        <bfChan> 0 |-> queue(100, ListItem(msg(ListItem(42)))) </bfChan>
        <nextPid> 1 </nextPid>
*/

/* send
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              $c [ 0 ] ! 42
              => .K
            </k>
            <env> lval($c,0) |-> bfPort(0) </env>
          </proc>
        </procs>
        <lock> #none </lock>
        <bfChan> 0 |-> queue(100, .List) </bfChan>
        <nextPid> 1 </nextPid>
*/

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
