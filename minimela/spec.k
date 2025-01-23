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

  syntax Id ::= "$a" [token] | "$b" [token] | "$c" [token]
  syntax Id ::= "$n" [token] | "$s" [token]


  claim <procs>
          <proc>
            <pid> 1 </pid>
            <k>
                do
                  :: 0 < $n ; $s = $s + $n ; $n = $n - 1
                  :: 0 >= $n ; break
                od
              => .K
            </k>
            <env>
              (lval($s,0) |-> loc(0))
              (lval($n,0) |-> loc(1))
            </env>
          </proc>
        </procs>
        <store>
          (0 |-> (S:Int => S +Int ((N +Int 1) *Int N /Int 2)))
          (1 |-> (N:Int => 0))
        </store>
        <lock> #none </lock>
    requires N >=Int 0


/*
  claim [invariant] :
        <procs>
          <proc>
            <pid> 1 </pid>
            <k>
                do
                  :: $c [ 0 ] ? $a ; $b = $b + 1
                od
            //  => .K
         ...</k>
            <env>
              (lval($a,0) |-> loc(0))
              (lval($b,0) |-> loc(1))
              (lval($c,0) |-> bfPort(0))
            </env>
          </proc>
        </procs>
        <store> (0 |-> 0) (1 |-> (B:Int => ?B')) </store>
        <bfChan> 0 |-> queue(_, (MSGL:List => ?MSGL')) </bfChan>
        <lock> #none </lock>
    ensures (B +Int size(MSGL)) ==K (?B' +Int size(?MSGL'))
    [trusted]

  claim [termination] :
        <procs>
          <proc>
            <pid> 1 </pid>
            <k>
                do
                  :: $c [ 0 ] ? $a ; $b = $b + 1
                od
           //   => .K
         ...</k>
            <env>
              (lval($a,0) |-> loc(0))
              (lval($b,0) |-> loc(1))
              (lval($c,0) |-> bfPort(0))
            </env>
          </proc>
        </procs>
        <store> (0 |-> 0) (1 |-> (B:Int => ?_)) </store>
        <bfChan> 0 |-> queue(_, (_ => .List)) </bfChan>
        <lock> #none </lock>
    [trusted]

  // bf recv
  claim <procs>
          <proc>
            <pid> 1 </pid>
            <k>
                do
                  :: $c [ 0 ] ? $a ; $b = $b + 1
                od
          //    => .K
            </k>
            <env>
              (lval($a,0) |-> loc(0))
              (lval($b,0) |-> loc(1))
              (lval($c,0) |-> bfPort(0))
            </env>
          </proc>
        </procs>
        <store> (0 |-> 0) (1 |-> (_ => ?B)) </store>
        <bfChan> 0 |-> queue(_, MSGL => .List) </bfChan>
        <lock> #none </lock>
    ensures ?B ==K size(MSGL)
*/

/*
  rule eval(C [ I:Int ] ?? EXPL, (lval(C, I) |-> bfPort(J)) ENV, STR, (J |-> queue(SIZE, MSGL)) BFC)
    =>
  eval(C [ I:Int ] ?? EXPL, (lval(C, I) |-> bfPort(J)) ENV, STR, (J |-> queue(SIZE, .List)) BFC)
  #Or (
    #Exists VL . #Exists MSGL' .
    eval(C [ I:Int ] ?? EXPL, (lval(C, I) |-> bfPort(J)) ENV, STR, (J |-> queue(SIZE, ListItem(msg(VL)) MSGL')) BFC)
  )
  // ensures size --
  [simplification]
*/

/* // channel assign
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              ($a [ 1 - 1 ] = $c [ 0 ]):Stmt
              => .K </k>
            <env> (lval($a,0) |-> rvPort(-1)) (lval($c,0) |-> rvPort(0)) </env>
          </proc>
        </procs>
        <lock> #none </lock>
*/


/* // rv channel
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              $a [ 0 ] ! 1 , 2 
              => .K </k>
            <env>
              (lval($a,0) |-> rvPort(I:Int))
              (lval($b,0) |-> loc(J:Int))
            </env>
          </proc>
          <proc>
            <pid> 1 </pid>
            <k>
              $a [ 0 ] ? 1 , $b
              => .K </k>
            <env>
              (lval($a,0) |-> rvPort(I:Int))
              (lval($b,0) |-> loc(J:Int))
            </env>
          </proc>
        </procs>
        <store> J |-> 0 </store>
        <bfChan> .Map </bfChan>
        <lock> #none </lock>
*/

/*  // int array decl
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              int $a [ 3 ] = 42
              => .K </k>
            <env>
              .Map => (
                (lval($a,0) |-> loc(?I0:Int))
                (lval($a,1) |-> loc(?I1:Int))
                (lval($a,2) |-> loc(?I2:Int))
              )
            </env>
          </proc>
        </procs> 
        <store>
          .Map => ((?I0 |-> 42) (?I1 |-> 42) (?I2 |-> 42))
        </store>
        <lock> #none </lock>
        <nextLoc> 0 => ?_ </nextLoc>
*/
 
/* // atomicity
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              atomic {
                $a = $a + 1;
                $a = $a + 1 
              }
              => .K </k>
            <env>
              (lval($a,0) |-> loc(0))
              (lval($b,0) |-> loc(1))
            </env>
          </proc>
          <proc>
            <pid> 1 </pid>
            <k>
              ($b = $a):Stmt
              => .K </k>
            <env>
              (lval($a,0) |-> loc(0))
              (lval($b,0) |-> loc(1))
            </env>
          </proc>
        </procs>
        <store>
          (0 |-> (0 => ?_:Int))
          (1 |-> (0 => ?B))
        </store>
        <lock> #none </lock>
    ensures (?B =/=K 1)
*/

/*  // simple concurrency
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              $a = $a + 1;
              $a = $a + 1 
              => .K </k>
            <env> (lval($a,0) |-> loc(0)) (lval($b,0) |-> loc(1)) </env>
          </proc>
          <proc>
            <pid> 1 </pid>
            <k>
              ($b = $a):Stmt
              => .K </k>
            <env> (lval($a,0) |-> loc(0)) (lval($b,0) |-> loc(1)) </env>
          </proc>
        </procs>
        <store> (0 |-> (0 => ?_:Int)) (1 |-> (0 => ?B)) </store>
    ensures (?B =/=K 1)
*/

/*  // loop invariant
  claim <procs>
          <proc>
            <pid> 0 </pid>
            <k>
              do
                :: $a < 3 ; $a = $a + 1
                :: $a >= 3 ; break
              od
             => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> (0 => ?I:Int) </store>
    ensures ?I <=Int 3
*/

/*  // select
  claim <procs>
          <proc>
            <k>
              if
                :: $a > 1 ; $a = 42  // true branch
                :: $a > 2 ; $a = 42  // true branch
                :: $a > 3 ; $a = 100 // false branch
              fi
             => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> (3 => 42) </store>
*/

/* // assign
  claim <procs>
          <proc>
            <k> (
              SetItem(choice(sil, ($a = 1):Stmt))
              SetItem(choice(sil, $a == 2))
              SetItem(choice(sil, $a == 3))
            ) => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> (42 => 1) </store>
*/


/* // choice for epxr
  claim <procs>
          <proc>
            <k> (
              SetItem(choice(sil, $a == 1))
              SetItem(choice(sil, $a == 2))
              SetItem(choice(sil, $a == 3))
            ) => .K ...</k>
            <env> lval($a,0) |-> loc(0) </env>
          </proc>
        </procs>
        <store> 0 |-> 2 </store>
*/


endmodule
