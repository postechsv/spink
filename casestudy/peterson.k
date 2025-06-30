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

module PETERSON
  imports VERIFICATION

  syntax Id ::= "$x" [token] | "$y" [token]
              | "$f0" [token] | "$f1" [token]
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
              (lval($x,0) |-> loc(I0))
              (lval($f0,0) |-> loc(I1))
              (lval($f1,0) |-> loc(I2))
              (lval($turn,0) |-> loc(I3))
              (lval($reg,0) |-> loc(I4)) // local
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
              (lval($x,0) |-> loc(I0))
              (lval($f0,0) |-> loc(I1))
              (lval($f1,0) |-> loc(I2))
              (lval($turn,0) |-> loc(I3))
              (lval($reg,0) |-> loc(I5)) // local
            </env>
       ...</proc>
        </procs>
        <store>
          (I0:Int |-> (0 => 2)) // x
          (I1:Int |-> (0 => ?_)) // f0
          (I2:Int |-> (0 => ?_)) // f1
          (I3:Int |-> (0 => ?_)) // turn
          (I4:Int |-> (0 => ?_)) // reg0
          (I5:Int |-> (0 => ?_)) // reg1
        </store>
        <lock> #none </lock>
        requires I0 =/=K I1 andBool I1 =/=K I2 andBool I2 =/=K I3 andBool I3 =/=K I4 andBool I4 =/=K I5  

endmodule 
