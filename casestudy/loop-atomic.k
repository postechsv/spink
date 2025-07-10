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

module LOOP-ATOMIC
  imports VERIFICATION

  syntax Id ::= "$x" [token]

 

  claim [loop]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k> //.K
              #normalize(.List)
              => ?_
            </k>
       ...</proc>
 
          <proc>... // monitor
            <pid> 0 </pid>
            <k> //true
              SetItem ( @[ true ~> #rel ] )
              => .K 
            </k>
       ...</proc>
 
          <proc>...
            <pid> 1 </pid>
            <k>
              //do
              //  :: atomic { $x[0] = $x[0] + 1 ; $x[0] = $x[0] + 1 }
              //  :: break
              //od
(
          SetItem ( @[ ($x [ 0 ] = $x [ 0 ] + 1):Stmt ~> ($x [ 0 ] = $x [ 0 ] + 1):Stmt ~> #rel ~> do :: atomic { $x [ 0 ] = $x [ 0 ] + 1 ; $x [ 0 ] = $x [ 0 ] + 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
          SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $x [ 0 ] = $x [ 0 ] + 1 ; $x [ 0 ] = $x [ 0 ] + 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
) 
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k>
              //do
              //  :: atomic { $x[0] = $x[0] + 1 ; $x[0] = $x[0] + 1 }
              //  :: break
              //od
(
          SetItem ( @[ ($x [ 0 ] = $x [ 0 ] + 1):Stmt ~> ($x [ 0 ] = $x [ 0 ] + 1):Stmt ~> #rel ~> do :: atomic { $x [ 0 ] = $x [ 0 ] + 1 ; $x [ 0 ] = $x [ 0 ] + 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
          SetItem ( @[ true ~> #rel ~> break ~> do :: atomic { $x [ 0 ] = $x [ 0 ] + 1 ; $x [ 0 ] = $x [ 0 ] + 1 ; .Seq } ; .Seq  :: break ; .Seq  .Optns od ~> .K ] )
)
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>
 
        <store>
          (0 |-> (N:Int => ?M))
        </store>

    requires N %Int 2 ==K 0
    ensures ?M %Int 2 ==K 0


  // the following lemma can be proven
  // it is need to prevent pid I to loop forever when pid J is done

  rule ( _I:Int ~> .K ) ==K ( #none ~> .K ) => false [simplification]

  // for some reason, this rule is necessary to prove the lemma
  rule load( I:Int ==Int I':Int , K ) => load(false, K) requires I =/=K I' [simplification]



  claim [loop-atomic-lemma]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k>
               #normalize(ListItem(0) ListItem(1) ListItem(2)) => ?_
            </k>
       ...</proc>
 
          <proc>... // monitor
            <pid> 0 </pid>
            <k> 
               (SetItem ( @[ true ~> #rel ~> .K ] ) ~> .K) => .K
            </k>
       ...</proc>
 
          <proc>... // pid I
            <pid> _I:Int </pid>
            <k>
              do
                :: atomic { $x[0] = $x[0] + 1 ; $x[0] = $x[0] + 1 }
                :: break
              od => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>... // pid J
            <pid> _J:Int </pid>
            <k> .K </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N:Int => ?M))
        </store>

    requires N %Int 2 ==K 0
    ensures ?M %Int 2 ==K 0
  //[trusted]

/*
  claim [loop-atomic-lemma2]:
        <procs>
          <proc>... // controller
            <pid> -1 </pid>
            <k>
               #normalize(ListItem(0) ListItem(1) ListItem(2)) => ?_
            </k>
       ...</proc>
 
          <proc>... // monitor
            <pid> 0 </pid>
            <k> 
               (SetItem ( @[ true ~> #rel ~> .K ] ) ~> .K) => .K
            </k>
       ...</proc>
 
          <proc>... // pid I
            <pid> 2 </pid>
            <k>
              do
                :: atomic { $x[0] = $x[0] + 1 ; $x[0] = $x[0] + 1 }
                :: break
              od => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>... // pid J
            <pid> 1 </pid>
            <k> .K </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>
        </procs>

        <lock> #none </lock>
        <active> ListItem(0) ListItem(1) ListItem(2) </active>

        <store>
          (0 |-> (N:Int => ?M))
        </store>

    requires N %Int 2 ==K 0
    ensures ?M %Int 2 ==K 0
  [trusted]
*/

endmodule
