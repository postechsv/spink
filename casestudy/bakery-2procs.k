requires "../promela.k"
requires "domains.md"

/*** this bakery3.k updates bakery2.k by generalizing N,N to N,M where N=M or N=M+1 ***/

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
              | "$crit" [token] | "$tick" [token]

  // for some reason, this rule is necessary to prove the lemma
 // rule load( I:Int ==Int I':Int , K ) => load(false, K) requires I =/=K I' [simplification]

  //rule ( _I:Int ~> .K ) ==K ( #none ~> .K ) => false [simplification]
endmodule

module BAKERY-1PROCS
  imports BAKERY

  claim [bakery1-mutex-ib]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k> #normalize(.List) => ?_ </k>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> SetItem ( @[ true ~> #rel ] ) => .K </k>
       ...</proc>
 
          <proc>...
            <pid> 1 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
             => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
  //[trusted] 


  claim [bakery1-mutex-bi]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k> #normalize(.List) => ?_ </k>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> SetItem ( @[ true ~> #rel ] ) => .K </k>
       ...</proc>
 
          <proc>...
            <pid> 1 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
             <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
             => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
  //[trusted] 
endmodule

module BAKERY-2PROCS
  imports BAKERY-1PROCS

  claim [bakery2-mutex-main]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: atomic { // idle -> wait(disp++)
                     $tick[0] = $disp[0] ;
                     $disp[0] = $disp[0] + 1
                   }
                 ; atomic { // wait(disp) -> crit
                     ($tick[0] == $serv[0]) ; 
                     $crit[0] = $crit[0] + 1
                   }
                 ; atomic { // crit -> idle
                     $serv[0] = $serv[0] + 1 ;
                     $crit[0] = $crit[0] - 1
                   }
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k>
              do
                :: atomic { // idle -> wait(disp++)
                     $tick[0] = $disp[0] ;
                     $disp[0] = $disp[0] + 1
                   }
                 ; atomic { // wait(disp) -> crit
                     ($tick[0] == $serv[0]) ; 
                     $crit[0] = $crit[0] + 1
                   }
                 ; atomic { // crit -> idle
                     $serv[0] = $serv[0] + 1 ;
                     $crit[0] = $crit[0] - 1
                   }
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> true => .K </k>
       ...</proc>
 
          <proc>... // controller
            <pid> -1 </pid>
            <k> .K => ?_ </k>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex



  claim [bakery2-mutex-ii]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k> #normalize(.List) => ?_ </k>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> SetItem ( @[ true ~> #rel ] ) => .K </k>
       ...</proc>
 
          <proc>...
            <pid> 1 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
             => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex



  claim [bakery2-mutex-iw]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k> #normalize(.List) => ?_ </k>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> SetItem ( @[ true ~> #rel ] ) => .K </k>
       ...</proc>
 
          <proc>...
            <pid> 1 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k> 
SetItem ( @[ $tick [ 0 ] == $serv [ 0 ] ~> $crit [ 0 ] = $crit [ 0 ] + 1 ~> #rel ~> .K ] ) ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (N => ?_TICK2)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
//[trusted] 

  claim [bakery-mutex-wi]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k> #normalize(.List) => ?_ </k>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> SetItem ( @[ true ~> #rel ] ) => .K </k>
       ...</proc>
 
          <proc>...
            <pid> 1 </pid>
            <k>
 SetItem ( @[ $tick [ 0 ] == $serv [ 0 ] ~> $crit [ 0 ] = $crit [ 0 ] + 1 ~> #rel ~> .K ] ) ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od
              => ?_ 
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(3))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (N => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
//[trusted] 

endmodule
