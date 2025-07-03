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

module LOOP
  imports VERIFICATION

  syntax Id ::= "$x" [token]

//  rule [seq2]:
//       <k> (S:Stmt ; S':Seq) => (S ~> S') ...</k> [simplification]
 

  claim [loop]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: $x[0]  = $x[0] + 2
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
                :: $x[0]  = $x[0] + 2
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

endmodule
