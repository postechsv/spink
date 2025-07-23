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

  claim [bakery1-mutex-ibb]:
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

          <proc>...
            <pid> 3 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
  [trusted] 


  claim [bakery1-mutex-bib]:
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
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
             => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>

          <proc>...
            <pid> 3 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
  [trusted] 


  claim [bakery1-mutex-bbi]:
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
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
             => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>


        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick2
        </store>

    ensures ?CRIT <=Int 1 // mutex
  [trusted] 


endmodule

module BAKERY-2PROCS-IIB
  imports BAKERY-1PROCS

/*
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
*/

//--------------------------------------//
// necessary circularity claims for iib //
//--------------------------------------//

  claim [bakery2-mutex-iib]:
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

          <proc>...
            <pid> 3 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
 
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted]


  claim [bakery2-mutex-iwb]:
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

          <proc>...
            <pid> 3 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (N => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted] 

  claim [bakery-mutex-wib]:
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

          <proc>...
            <pid> 3 </pid>
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (N => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted] 

endmodule


module BAKERY-2PROCS-IBI
  imports BAKERY-1PROCS

//--------------------------------------//
// necessary circularity claims for ibi //
//--------------------------------------//

  claim [bakery2-mutex-ibi]:
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
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted]


  claim [bakery2-mutex-ibw]:
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
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>

          <proc>...
            <pid> 3 </pid>
            <k> 
SetItem ( @[ $tick [ 0 ] == $serv [ 0 ] ~> $crit [ 0 ] = $crit [ 0 ] + 1 ~> #rel ~> .K ] ) ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (N => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted] 


  claim [bakery-mutex-wbi]:
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
            <k> .K </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(4))
            </env>
       ...</proc>

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (N => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted] 
endmodule


module BAKERY-2PROCS-BII
  imports BAKERY-1PROCS

//--------------------------------------//
// necessary circularity claims for bii //
//--------------------------------------//

  claim [bakery2-mutex-bii]:
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

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted]


  claim [bakery2-mutex-biw]:
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

          <proc>...
            <pid> 3 </pid>
            <k> 
SetItem ( @[ $tick [ 0 ] == $serv [ 0 ] ~> $crit [ 0 ] = $crit [ 0 ] + 1 ~> #rel ~> .K ] ) ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (N => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted] 

  claim [bakery-mutex-bwi]:
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

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // stat1
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (N => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted] 

endmodule


module BAKERY-2PROCS
  imports BAKERY-2PROCS-IIB
  imports BAKERY-2PROCS-IBI
  imports BAKERY-2PROCS-BII
endmodule


module BAKERY-3PROCS
  imports BAKERY-2PROCS

  claim [bakery3-mutex-iii]:
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

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N:Int => ?_DISP:Int)) // disp
          (1 |-> (N => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    //[trusted]

  claim [bakery3-mutex-wii]:
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

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (N => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted]

  claim [bakery3-mutex-iwi]:
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

          <proc>...
            <pid> 3 </pid>
            <k>
        SetItem ( @[ $tick [ 0 ] = $disp [ 0 ] ~> $disp [ 0 ] = $disp [ 0 ] + 1 ~> #rel ~> atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
        SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
              => ?_
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (N => ?_TICK2)) // tick2
          (5 |-> (_ => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted]

  claim [bakery3-mutex-iiw]:
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

          <proc>...
            <pid> 3 </pid>
            <k>
 SetItem ( @[ $tick [ 0 ] == $serv [ 0 ] ~> $crit [ 0 ] = $crit [ 0 ] + 1 ~> #rel ~> .K ] ) ~> atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ~> do :: atomic { $tick [ 0 ] = $disp [ 0 ] ; $disp [ 0 ] = $disp [ 0 ] + 1 ; .Seq } ; atomic { $tick [ 0 ] == $serv [ 0 ] ; $crit [ 0 ] = $crit [ 0 ] + 1 ; .Seq } ; atomic { $serv [ 0 ] = $serv [ 0 ] + 1 ; $crit [ 0 ] = $crit [ 0 ] - 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od
              => ?_ 
            </k>
            <env>
              (lval($disp,0) |-> loc(0))
              (lval($serv,0) |-> loc(1))
              (lval($crit,0) |-> loc(2))
              (lval($tick,0) |-> loc(5))
            </env>
       ...</proc>

        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) ListItem(3) </active>

        <store>
          (0 |-> (N +Int 1 => ?_DISP:Int)) // disp
          (1 |-> (N:Int => ?_SERV:Int)) // serv
          (2 |-> (0 => ?CRIT)) // crit
          (3 |-> (_ => ?_TICK1)) // tick1
          (4 |-> (_ => ?_TICK2)) // tick2
          (5 |-> (N => ?_TICK3)) // tick3
        </store>

    ensures ?CRIT <=Int 1 // mutex
    [trusted]

  //claim [bakery3-mutex-wwi]:
  //claim [bakery3-mutex-wiw]:
  //claim [bakery3-mutex-iww]:
endmodule
