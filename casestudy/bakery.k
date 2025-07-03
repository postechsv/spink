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

module BAKERY
  imports VERIFICATION

  syntax Id ::= "$disp" [token] | "$serv" [token]
              | "$stat" [token] | "$tick" [token]

  claim [bakery-mutex]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: atomic { // idle -> wait(disp++)
                     $stat[0] == 0 ;
                     $tick[0] = $disp[0] ;
                     $disp[0] = $disp[0] + 1 ;
                     $stat[0] = 1 // goto wait
                   }
                :: atomic { // wait(disp) -> crit
                     ($stat[0] == 1) ; ($tick[0] == $serv[0]) ; 
                     $stat[0] = 2 // goto crit
                   }
                :: atomic { // crit -> idle
                     $stat[0] == 2 ;
                     $serv[0] = $serv[0] + 1 ;
                     $stat[0] = 0 // goto idle
                   }
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k>
              do
                :: atomic { // idle -> wait(disp++)
                     $stat[0] == 0 ;
                     $tick[0] = $disp[0] ;
                     $disp[0] = $disp[0] + 1 ;
                     $stat[0] = 1 // goto wait
                   }
                :: atomic { // wait(disp) -> crit
                     ($stat[0] == 1) ; ($tick[0] == $serv[0]) ; 
                     $stat[0] = 2 // goto crit
                   }
                :: atomic { // crit -> idle
                     $stat[0] == 2 ;
                     $serv[0] = $serv[0] + 1 ;
                     $stat[0] = 0 // goto idle
                   }
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(4))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> true => .K </k>
       ...</proc>
 
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (N:Int => ?DISP:Int)) // disp
          (1 |-> (N => ?SERV:Int)) // serv
          (2 |-> (0 => ?STAT1)) // stat1
          (3 |-> (_ => ?_)) // tick1
          (4 |-> (0 => ?STAT2)) // stat2
          (5 |-> (_ => ?_)) // tick2
        </store>

    ensures ?STAT1 =/=K 2 orBool ?STAT2 =/=K 2 // mutex
            // (?SERV <=Int ?DISP) andBool (?DISP <=Int ?SERV +Int 2)
            //andBool (?SERV <=Int ?T1) andBool (?T1 <=Int ?SERV +Int 1) // more stronger assertion

endmodule
