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

  syntax Id ::= "$p1" [token] | "$p2" [token]
              | "$disp" [token] | "$serv" [token]
              | "$stat" [token] | "$tick" [token]

  // example2) bakery - nonstarvation
  claim <procs>
          <proc>
            <pid> 1 </pid>
            <name> $p1 </name>
            <k>
              do
                :: atomic {
                     $stat == 0 ;
                     $stat[0] = 1 ;
                     $tick[0] = $disp ; // wait(disp)
                     $disp[0] = $disp + 1
                   }
                :: atomic {
                     ($stat == 1) && ($tick == $serv) ; 
                     $stat[0] = 2 // crit
                   }
                :: atomic {
                     $stat == 2 ;
                     $stat[0] = 0 ; // idle
                     $serv[0] = $serv + 1
                   }
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
          </proc>

          <proc>
            <pid> 2 </pid>
            <name> $p2 </name>
            <k>
              do
                :: atomic {
                     $stat == 0 ;
                     $stat[0] = 1 ;
                     $tick[0] = $disp ; // wait(disp)
                     $disp[0] = $disp + 1
                   }
                :: atomic {
                     ($stat == 1) && ($tick == $serv) ; 
                     $stat[0] = 2 // crit
                   }
                :: atomic {
                     $stat == 2 ;
                     $stat[0] = 0 ; // idle
                     $serv[0] = $serv + 1
                   }
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(4))
              (lval($tick,0) |-> loc(5))
            </env>
          </proc>
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (N:Int => ?DISP:Int)) // disp
          (1 |-> (N => ?SERV:Int)) // serv
          (2 |-> (0 => 2)) // stat1
          (3 |-> (_ => ?_)) // tick1
          (4 |-> (0 => ?_)) // stat2
          (5 |-> (_ => ?_)) // tick2
        </store>

    ensures (?SERV <=Int ?DISP) andBool (?DISP <=Int ?SERV +Int 2)
            //andBool (?SERV <=Int ?T1) andBool (?T1 <=Int ?SERV +Int 1) // more stronger assertion


  // example2) bakery FIXME: this is meaningless! trivially true because the initial state already satisfies the condition
/*
  claim <procs>
          <proc>
            <pid> 1 </pid>
            <name> $p1 </name>
            <k>
              do
                :: atomic {
                     $stat == 0 ;
                     $stat[0] = 1 ;
                     $tick[0] = $disp ; // wait(disp)
                     $disp[0] = $disp + 1
                   }
                :: atomic {
                     ($stat == 1) && ($tick == $serv) ; 
                     $stat[0] = 2 // crit
                   }
                :: atomic {
                     $stat == 2 ;
                     $stat[0] = 0 ; // idle
                     $serv[0] = $serv + 1
                   }
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
          </proc>

          <proc>
            <pid> 2 </pid>
            <name> $p2 </name>
            <k>
              do
                :: atomic {
                     $stat == 0 ;
                     $stat[0] = 1 ;
                     $tick[0] = $disp ; // wait(disp)
                     $disp[0] = $disp + 1
                   }
                :: atomic {
                     ($stat == 1) && ($tick == $serv) ; 
                     $stat[0] = 2 // crit
                   }
                :: atomic {
                     $stat == 2 ;
                     $stat[0] = 0 ; // idle
                     $serv[0] = $serv + 1
                   }
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(4))
              (lval($tick,0) |-> loc(5))
            </env>
          </proc>
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (0 => ?DISP:Int)) // disp
          (1 |-> (0 => ?SERV:Int)) // serv
          (2 |-> (0 => ?_)) // stat1
          (3 |-> (-1 => ?_)) // tick1
          (4 |-> (0 => ?_)) // stat2
          (5 |-> (-1 => ?_)) // tick2
        </store>
        ensures (?DISP ==K ?SERV) orBool (?DISP ==K ?SERV +Int 1)
*/

  // example1) summation
/*
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
*/
endmodule
