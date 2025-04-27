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

  syntax Id ::= "$x" [token] | "$y" [token]
              | "$n" [token] | "$s" [token]



/*
  claim [summation-inv]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
SetItem ( @[ 0 < $n ~> #rel ~> $s [ 0 ] = $s + $n ; $n [ 0 ] = $n - 1 ; .Seq ~> do :: 0 < $n ; $s [ 0 ] = $s + $n ; $n [ 0 ] = $n - 1 ; .Seq  :: 0 >= $n ; break ; .Seq  .Optns od ~> .K ] )
          SetItem ( @[ 0 >= $n ~> #rel ~> break ; .Seq ~> do :: 0 < $n ; $s [ 0 ] = $s + $n ; $n [ 0 ] = $n - 1 ; .Seq  :: 0 >= $n ; break ; .Seq  .Optns od ~> .K ] )
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(0))
              (lval($n,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
    requires N >Int 0 


  claim [summation]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
                :: 0 >= $n ; break
              od ; .Seq
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(0))
              (lval($n,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
    requires N >Int 0 
*/

/*
  claim [assign]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k> ($x = 42):Stmt => .K </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (_ => 42))
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
*/


  syntax Id ::= "$f0" [token] | "$f1" [token]
              | "$turn" [token] | "$reg" [token]


  claim [peterson]:
        <procs>
          <proc>...
            <pid> 0 </pid>
            <k> 
              $f0 = 1 ; $turn = 1 ;
              ($f1 != 1) || ($turn != 1) ;
              $reg = $x + 1 ; $x = $reg ;
              $f0 = 0
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($f0,0) |-> loc(1))
              (lval($f1,0) |-> loc(2))
              (lval($turn,0) |-> loc(3))
              (lval($reg,0) |-> loc(4)) // local
            </env>
       ...</proc>
          <proc>...
            <pid> 1 </pid>
            <k> 
              $f1 = 1 ; $turn = 0 ;
              ($f0 != 1) || ($turn != 0) ;
              $reg = $x + 1 ; $x = $reg ;
              $f1 = 0
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($f0,0) |-> loc(1))
              (lval($f1,0) |-> loc(2))
              (lval($turn,0) |-> loc(3))
              (lval($reg,0) |-> loc(5)) // local
            </env>
       ...</proc>
        </procs>
        <store>
          (0 |-> (0 => 2)) // x
          (1 |-> (0 => ?_)) // f0
          (2 |-> (0 => ?_)) // f1
          (3 |-> (0 => ?_)) // turn
          (4 |-> (0 => ?_)) // reg0
          (5 |-> (0 => ?_)) // reg1
        </store>
        <lock> #none </lock>


/*
  syntax Id ::= "$p1" [token] | "$p2" [token]
              | "$disp" [token] | "$serv" [token]
              | "$stat" [token] | "$tick" [token]


  claim <procs>
          <proc>...
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
                   } ; break
              od ; .Seq
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
                   } ; break
              od ; .Seq
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($stat,0) |-> loc(4))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (N:Int => ?DISP:Int)) // disp
          (1 |-> (N => ?SERV:Int)) // serv
          (2 |-> (0 => 2)) // stat1
          (3 |-> (-1 => ?_)) // tick1
          (4 |-> (0 => ?_)) // stat2
          (5 |-> (-1 => ?_)) // tick2
        </store>

    ensures (?SERV <=Int ?DISP) andBool (?DISP <=Int ?SERV +Int 2)
            //andBool (?SERV <=Int ?T1) andBool (?T1 <=Int ?SERV +Int 1) // more stronger assertion
*/
endmodule 
