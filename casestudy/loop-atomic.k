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
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: $x[0] = $x[0] + 2
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>...
            <pid> 2 </pid>
            <k>
              do
                :: $x[0] = $x[0] + 2
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> true => .K </k>
       ...</proc>
 
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (N:Int => ?M)) // disp
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
          <proc>...
            <pid> I:Int </pid>
            <k>
              do
                :: atomic { $x[0] = $x[0] + 1 ; $x[0] = $x[0] + 1 }
                :: break
              od
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>...
            <pid> J:Int </pid>
            <k> .K </k>
            <env>
              (lval($x,0) |-> loc(0))
            </env>
       ...</proc>

          <proc>... // monitor
            <pid> 0 </pid>
            <k> true => .K </k>
       ...</proc>
 
        </procs>

        <lock> #none </lock>

        <store>
          (0 |-> (N:Int => ?M)) // disp
        </store>

    requires I =/=Int 0 andBool J =/=Int 0 andBool I =/=Int J andBool N %Int 2 ==K 0
    ensures ?M %Int 2 ==K 0
  //[trusted]

endmodule
