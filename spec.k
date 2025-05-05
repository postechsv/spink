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


  claim [example-inv]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
//do
//   :: true ; break
//   :: $x > 0 ; $x = $x + 4
//   :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 }
//od ; .Seq
(
          SetItem ( @[ $x < 10 ~> $x = $x + 1 ; $x = $x + 1 ; .Seq ~> #rel ~> .Seq ~> do :: true ; break ; .Seq  :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] )
          SetItem ( @[ $x > 0 ~> #rel ~> $x = $x + 4 ; .Seq ~> do :: true ; break ; .Seq  :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] )
          SetItem ( @[ true ~> #rel ~> break ; .Seq ~> do :: true ; break ; .Seq  :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] ) ~> .K
)
             => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k>
              //($y = $x):BasicStmt ; .Seq 
(SetItem ( @[ ($y = $x):Stmt ~> #rel ~> .K ] ) ~> .K)
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (X:Int => ?_))
          (1 |-> (Y:Int => ?Y':Int))
        </store>
        <lock> #none </lock>
    requires X %Int 2 ==K 0 andBool Y %Int 2 ==K 0
    ensures ?Y' %Int 2 ==K 0 


  claim [example]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
// if
// :: $x < $y ; $x = $x + 2
// :: do
//    :: true ; break
//    :: $x > 0 ; $x = $x + 4
//    :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 }
//    od
// fi ; .Seq
(
          SetItem ( @[ $x < 10 ~> $x = $x + 1 ; $x = $x + 1 ; .Seq ~> #rel ~> .Seq ~> do :: true ; break ; .Seq  :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] )
          SetItem ( @[ $x < $y ~> #rel ~> $x = $x + 2 ; .Seq ~> .K ] )
          SetItem ( @[ $x > 0 ~> #rel ~> $x = $x + 4 ; .Seq ~> do :: true ; break ; .Seq  :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] )
          SetItem ( @[ true ~> #rel ~> break ; .Seq ~> do :: true ; break ; .Seq  :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] ) ~> .K
)
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k>
              //($y = $x):BasicStmt ; .Seq 
(SetItem ( @[ ($y = $x):Stmt ~> #rel ~> .K ] ) ~> .K)
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (X2:Int => ?_))
          (1 |-> (Y2:Int => ?Y2':Int))
        </store>
        <lock> #none </lock>
    requires X2 %Int 2 ==K 0 andBool Y2 %Int 2 ==K 0
    ensures ?Y2' %Int 2 ==K 0 


/*
  syntax Id ::= "$x" [token] | "$y" [token]
              | "$n" [token] | "$s" [token]


  claim [example-inv]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
//do
//   :: $x > 0 ; $x = $x + 4
//   :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 }
//od ; .Seq
          (SetItem ( @[ $x < 10 ~> $x = $x + 1 ; $x = $x + 1 ; .Seq ~> #rel ~> .Seq ~> do :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] )
          SetItem ( @[ $x > 0 ~> #rel ~> $x = $x + 4 ; .Seq ~> do :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] ) ~> .K)
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k>
              //($y = $x):BasicStmt ; .Seq 
(SetItem ( @[ ($y = $x):Stmt ~> #rel ~> .K ] ) ~> .K)
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (X:Int => ?_))
          (1 |-> (Y:Int => ?Y':Int))
        </store>
        <lock> #none </lock>
    requires X %Int 2 ==K 0 andBool Y %Int 2 ==K 0
    ensures ?Y' %Int 2 ==K 0 
    [trusted]



  claim [example]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
// if
// :: $x < $y ; $x = $x + 2
// :: do
//    :: $x > 0 ; $x = $x + 4
//    :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 }
//    od
// fi ; .Seq
          (SetItem ( @[ $x < 10 ~> $x = $x + 1 ; $x = $x + 1 ; .Seq ~> #rel ~> .Seq ~> do :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] )
          SetItem ( @[ $x < $y ~> #rel ~> $x = $x + 2 ; .Seq ~> .K ] )
          SetItem ( @[ $x > 0 ~> #rel ~> $x = $x + 4 ; .Seq ~> do :: $x > 0 ; $x = $x + 4 ; .Seq  :: atomic { $x < 10 ; $x = $x + 1 ; $x = $x + 1 ; .Seq } ; .Seq  .Optns od ~> .Seq ~> .K ] ) ~> .K)
              => ?_
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
          <proc>...
            <pid> 2 </pid>
            <k>
              //($y = $x):BasicStmt ; .Seq 
(SetItem ( @[ ($y = $x):Stmt ~> #rel ~> .K ] ) ~> .K)
              => .K
            </k>
            <env>
              (lval($x,0) |-> loc(0))
              (lval($y,0) |-> loc(1))
            </env>
       ...</proc>
        </procs>

        <store>
          (0 |-> (X2:Int => ?_))
          (1 |-> (Y2:Int => ?Y2':Int))
        </store>
        <lock> #none </lock>
    requires X2 %Int 2 ==K 0 andBool Y2 %Int 2 ==K 0
    ensures ?Y2' %Int 2 ==K 0 
*/

/*
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
*/

/*
  syntax Id ::= "$x" [token] | "$y" [token]
              | "$n" [token] | "$s" [token]

  claim [summation]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
            //  do
            //    :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
            //    :: 0 >= $n ; break
            //  od ; .Seq
  
SetItem ( @[ 0 < $n ~> #rel ~> $s [ 0 ] = $s + $n ; $n [ 0 ] = $n - 1 ; .Seq ~> do :: 0 < $n ; $s [ 0 ] = $s + $n ; $n [ 0 ] = $n - 1 ; .Seq  :: 0 >= $n ; break ; .Seq  .Optns od ~> .K ] )
          SetItem ( @[ 0 >= $n ~> #rel ~> break ; .Seq ~> do :: 0 < $n ; $s [ 0 ] = $s + $n ; $n [ 0 ] = $n - 1 ; .Seq  :: 0 >= $n ; break ; .Seq  .Optns od ~> .K ] )
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(I0:Int))
              (lval($n,0) |-> loc(I1:Int))
            </env>
       ...</proc>
        </procs>

        <store>
          (I0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (I1 |-> (N:Int => 0))
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


endmodule 
