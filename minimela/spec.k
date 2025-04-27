requires "minimela.k"
requires "domains.md"

module SPEC-SYNTAX
  imports MINIMELA-SYNTAX
endmodule

module VERIFICATION
  imports K-EQUAL
  imports SPEC-SYNTAX
  imports MINIMELA
  imports MAP-SYMBOLIC
endmodule

module SPEC
  imports VERIFICATION

  syntax Id ::= "$x" [token] | "$y" [token]
              | "$n" [token] | "$s" [token]

  claim [summation]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
                :: 0 >= $n ; break
              od
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



/*
  claim [summation]:
        <procs>
          <proc>...
            <pid> 1 </pid>
            <k>
              do
                :: 0 < $n ; $s[0] = $s + $n ; $n[0] = $n - 1
                :: 0 >= $n ; break
              od
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

  syntax Id ::= "$f0" [token] | "$f1" [token]
              | "$turn" [token] | "$reg" [token]

  claim [peterson]:
        <procs>
          <proc>...
            <pid> 0 </pid>
            <k>( 
              ($f0 = 1):Stmt ~> ($turn = 1):Stmt ~>
              (($f1 != 1) || ($turn != 1)):Stmt ~>
              ($reg = $x + 1):Stmt ~> ($x = $reg):Stmt ~>
              ($f0 = 0):Stmt
              ) => .K
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
            <k> (
              ($f1 = 1):Stmt ~> ($turn = 0):Stmt ~>
              (($f0 != 1) || ($turn != 0)):Stmt ~>
              ($reg = $x + 1):Stmt ~> ($x = $reg):Stmt ~>
              ($f1 = 0):Stmt
              ) => .K
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
*/ 
endmodule 
