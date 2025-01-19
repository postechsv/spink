module MINIMELA-SYNTAX
  imports DOMAINS-SYNTAX

  //syntax Spec ::= List{Mdle, " "}

  syntax Spec ::= Proc
                | Decl
                | Spec Spec [left]

  syntax Proc ::=  Active "proctype" Id "(" Decls ")" "{" Stmt "}"
                 | "proctype" Id "(" Decls ")" "{" Stmt "}"

  syntax Active ::= "active" | "active" "[" Const "]"

  syntax Decl ::= Type Ivar

  syntax Decls ::= List{Decl, ";"}

  syntax Type ::= "int" | "bool" | "chan"

  syntax Types ::= List{Type, ","}

  syntax BasicStmt ::= Decl | Expr | "run" Id "(" Exprs ")"
                     | Id "=" Expr [macro] // Assign-sugar
                     | Id "[" Expr "]" "=" Expr // Assign
                     | Id "[" Expr "]" "!" Exprs // Send
                     | Id "[" Expr "]" "?" Exprs // Recv

                     | "skip"

  syntax Stmt ::= BasicStmt | Stmt ";" | Stmt ";" Stmt [left, prefer]
                | "atomic" "{" Stmt "}"
                | "if" Optns "fi" | "do" Optns "od"
                | "break" 

//  syntax Stmt ::= "skip" | Stmt ";" | Stmt ";" Stmt [left, prefer] | Decl | Const | Expr
//                | Vref "=" Expr | "run" Id "(" Exprs ")"  | "atomic" "{" Stmt "}" | "if" Optns "fi"
//                | Vref "!" Exprs | Vref "?" Exprs

  syntax Expr ::= Const | Vref
                | "(" Expr ")" [bracket]
                | "-" Expr | "!" Expr
                | Expr "+" Expr | Expr "-" Expr | Expr "*" Expr | Expr "/" Expr 
                | Expr "<" Expr | Expr "<=" Expr | Expr ">" Expr | Expr ">=" Expr 
                | Expr "&&" Expr | Expr "||" Expr | Expr "==" Expr | Expr "!=" Expr 
                | full(Vref) | empty(Vref) | nfull(Vref) | nempty(Vref)
                | Id "[" Expr "]" "??" Exprs // Recv Poll (only for buf chans)


  syntax Exprs ::= List{Expr, ","}

  syntax Optn ::= "::" Stmt

  syntax Optns ::= List{Optn, ""}

  syntax Ivar ::= Ivar "," Ivar | Vref
                | Vref "=" Expr
                | Vref "=" "[" Const "]" "of" "{" Types "}"

  syntax Vref ::= Id | Id "[" Expr "]"

  syntax Const ::= Value

  syntax Value ::= Int | Bool

  syntax Id ::= "#Configurator" [token]

endmodule

module MINIMELA-CONFIG
  imports MINIMELA-SYNTAX
  imports DOMAINS

  syntax Lock ::= Int | "#none"

  configuration <T color="yellow">
/*                  <proctypes>
                    <proctype multiplicity="*" type="Map" initial="">
                      <procName> #Configurator </procName>
                      <procParams> .Decls </procParams>
                      <procBody> skip:Stmt </procBody> // skip:BasicStmt doesn't allow Stmt's in general
                      <gotoMap> .Map </gotoMap>
                    </proctype>
                  </proctypes>
*/
                  <procs> // active procs
                    <proc multiplicity="*" type="Map" color="orange" initial="">
                      <pid> -1 </pid>
                      <k color="green"> $PGM:Spec </k>
                      <env color="LightSalmon"> .Map </env>
                    </proc>
                  </procs> 

                  <store color="Salmon"> .Map </store>
                  <bfChan color="Salmon"> .Map </bfChan>

                  <lock> #none </lock>
                  <nextLoc> 0 </nextLoc>
                 // <nextPid> 0 </nextPid>

                </T>

endmodule

module MINIMELA
  imports MINIMELA-CONFIG

  /****************
  BASIC DEFINITIONS
  *****************/


  syntax KItem ::= "null" | loc(Int) | lval(Id, Int)
                 | choice(SEffect, K) // Effecful Choice

//  syntax K ::= dupKItems(KItem, Int) [function]
//  rule dupKItems(KI, 1) => KI
//  rule dupKItems(KI, N) => KI ~> dupKItems(KI, N -Int 1) [owise]

  syntax Value ::= eval(Expr, Map, Map, Map) [function]

  rule eval(V:Value, _, _, _) => V

  rule eval(X:Id, ENV, STR, BFC) => eval(X[0], ENV, STR, BFC) // desugar
  rule eval(X[IEXP], ENV, STR, BFC) => eval(X [ eval(IEXP, ENV, STR, BFC) ], ENV, STR, BFC) [owise] // i.e. IEXP not Int

  // Look-Up
  rule eval(X[I:Int], (lval(X, I) |-> loc(L)) _ENV, (L |-> V) _STR, _BFC) => V // loc
  rule eval(X[I:Int], (lval(X, I) |-> bfPort(J)) _ENV, _STR, _BFC) => bfPort(J) // buf chan
  rule eval(X[I:Int], (lval(X, I) |-> rvPort(J)) _ENV, _STR, _BFC) => rvPort(J) // rv chan

  // Arith Expr
  rule eval(E1 == E2, ENV, STR, BFC) => eval(E1, ENV, STR, BFC) ==K eval(E2, ENV, STR, BFC)
  rule eval(E1 + E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int +Int {eval(E2, ENV, STR, BFC)}:>Int
  rule eval(E1 - E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int -Int {eval(E2, ENV, STR, BFC)}:>Int
  rule eval(E1 < E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int <Int {eval(E2, ENV, STR, BFC)}:>Int
  rule eval(E1 <= E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int <=Int {eval(E2, ENV, STR, BFC)}:>Int
  rule eval(E1 > E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int >Int {eval(E2, ENV, STR, BFC)}:>Int
  rule eval(E1 >= E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int >=Int {eval(E2, ENV, STR, BFC)}:>Int

  // Chan Poll - TODO
  rule eval(nfull(_), _ENV, _STR, _BFC) => true

  // Poll
  rule eval(C [ I:Int ] ?? EXPL, (lval(C, I) |-> bfPort(J)) _ENV, _STR, (J |-> queue(_, ListItem(msg(VL)) _Q)) _BFC)
    => true requires matchMsg(EXPL, VL)
  rule eval(_ [ _:Int ] ?? _, _ENV, _STR, _BFC) => false [owise]


  // evalList - FIXME eval with brackets e.g. c ! (1 + 1) , (1 + 2) doesn't work
  //rule eval(( E:Expr ), ENV, STR, BFC) => eval(E, ENV, STR, BFC)
  syntax List ::= evalList(Exprs, Map, Map, Map) [function]
  rule evalList((E , E' , EL), ENV, STR, BFC) => ListItem(eval(E, ENV, STR, BFC)) evalList((E', EL), ENV, STR, BFC)
  rule evalList((E , .Exprs), ENV, STR, BFC) => ListItem(eval(E, ENV, STR, BFC))



  // Spec
  /* rule S1:Spec S2:Spec => S1 ~> S2 */

  // Decl
  /* rule T:Type I1:Ivar , I2:Ivar => T I1 ~> T I2 */


  // Decl for value types
  /* rule T:Type X:Id => T (X [ 1 ]) */ // desugar
  /* rule _:Type _:Id [ 0 ] => .K */
  /* rule <k> T:Type X:Id [ I:Int ] => T X [ I -Int 1 ] ...</k>
       <env> Env => Env[lval(X, I -Int 1) <- loc(L)] </env> 
       <store>... .Map => loc(L) |-> 0 ...</store>
       <nextLoc> L => L +Int 1 </nextLoc> [owise] */ // L may not be consecutive: int x[2] || int y[2]

  // Decl for Proc
  /* rule active proctype X:Id ( DL:Decls ) { S:Stmt }
    => active [ 1 ] proctype X:Id ( DL:Decls ) { S:Stmt } */ // sugar
  //rule active [ 0 ] proctype _ ( _ ) { _ } => .K
  /* rule active [ I:Int ] proctype X:Id ( DL:Decls ) { S:Stmt } 
    => proctype X:Id ( DL:Decls ) { S:Stmt } ~> dupKItems(run X ( .Exprs ), I) */

  // Proctype
  /* rule <k> proctype X:Id ( DL:Decls ) { S:Stmt } => .K ...</k>
       (.Bag => <proctype>...
                  <procName> X </procName>
                  <procParams> DL </procParams>
                  <procBody> S </procBody>
                ...</proctype>) */

  // Done
  rule <k> (SetItem ( choice ( _ , .K ) ) => .Set) ...</k>
  rule <k> (.Set:K => .K) ...</k>


  // Lift
  rule S:Stmt => SetItem(choice(sil, S))

  /*******************************************************
       Control Flow 
  *******************************************************/
 
  // Sequence
  rule <k> SetItem(choice(_E, ((S1 ; S2):Stmt => S1 ~> S2) ~> _K)) _:Set ...</k>

  // Flatten
  syntax Set ::= flatten(SEffect, Optns, K) [function]
  rule flatten(E, (:: S) OPTL, K) => SetItem(choice(E, S ~> K)) flatten(E, OPTL, K)
  rule flatten(_E, .Optns, _K) => .Set

  // Select
  rule <k> (SetItem(choice(E, if OPTL fi ~> K)) => flatten(E, OPTL, K)) _:Set ...</k>

  // Loop
  rule <k> SetItem(choice(_E, (.K => if OPTL fi) ~> do OPTL od ~> _K)) _:Set ...</k>

  // break
  rule <k> SetItem(choice(_E, ((break ~> do _ od) => .K) ~> _K)) _:Set ...</k>
  rule <k> SetItem(choice(_E, break ~> (_:Stmt => .K) ~> _K)) _:Set ...</k> [owise] // propagate

  // Locks
  syntax SEffect ::= "sil" | "acq"
  syntax KItem ::= "#rel"

  // Atomic
  // outermost atomic
  rule <k> 
         SetItem(choice(_ => acq, 
           (atomic { S } => (S ~> #rel))
           ~> _K))
         _:Set
    ...</k>

  // inner atomic - ignore
  rule <pid> PID:Int </pid>
       <k> 
         SetItem(choice(_, 
           (atomic { S } => S)
           ~> _K))
         _:Set
    ...</k>
       <lock> PID </lock>

  // Rel
  rule <k> 
         SetItem(choice(_, (#rel => .K) ~> _K))
         _:Set // this may not be necessary
    ...</k>
       <lock> _ => #none </lock>



  /*******************************************************
        BASIC ACTIONS (BasicStmt)
  *******************************************************/

  // getLock : result of applying EFF on LCK for PID
  syntax Lock ::= getLock(SEffect, Lock, Int) [function]
  rule getLock(sil, #none, _PID) => #none
  rule getLock(_EFF, _LCK, PID) => PID [owise]

  // Expr
  rule <k> SetItem(choice(_, (EXP:Expr => .K) ~> _)) (_:Set => .Set) ...</k>
       <env> ENV </env>  <store> STR </store>  <bfChan> BFC </bfChan>
    requires eval(EXP, ENV, STR, BFC) ==K true

  // Assign - TODO: eval(I)
  rule (X:Id = V):Stmt => (X [ 0 ] = V):Stmt // desugar
  rule <pid> PID </pid>
       <k>
         SetItem(choice(EFF => sil, // init side-effect
           ((X [ I:Int ] = EXP):Stmt => .K) ~> _K))
         (_:Set => .Set) // side-effect : choose
    ...</k>
       <env> (lval(X, I) |-> loc(L)) ENV </env>
       <store> STR => STR[L <- eval(EXP, (lval(X, I) |-> loc(L)) ENV, STR, BFC)] </store>
       <bfChan> BFC </bfChan>
       <lock> LCK => getLock(EFF, LCK, PID) </lock> // side-effect : acquire
    requires LCK ==K #none orBool LCK ==K PID
    //requires ENV' := (lval(X, I) |-> loc(L)) ENV // this does not work :(

  // Decl - TODO for channels
  rule T:Type X:Id => (T X [ 1 ]) // desugar
  // rule T X, IVAR => T X ; T IVAR // desugar
  // canonical form: T X [ I ] = EXP
  rule <pid> PID </pid>
       <k>
         SetItem(choice(EFF => sil, // init side-effect
           (_T:Type X [ I:Int ] = EXP => .K) ~> _K))
         (_:Set => .Set) // side-effect : choose
    ...</k>
       <env> ENV (.Map => getArrayEnv(X,I,L)) </env>
       <store> STR (.Map => L ... (L +Int I -Int 1) |-> eval(EXP, ENV, STR, BFC)) </store>
       <bfChan> BFC </bfChan>
       <lock> LCK => getLock(EFF, LCK, PID) </lock> // side-effect : acquire
       <nextLoc> L => L +Int I </nextLoc>
    requires LCK ==K #none orBool LCK ==K PID

  // (lval(X, 0) |-> L) ... (lval(X, I - 1) |-> L + I - 1) (used in Decl)
  syntax Map ::= getArrayEnv(Id, Int, Int) [function]
  rule getArrayEnv(X, 1, L) => (lval(X, 0) |-> loc(L))
  rule getArrayEnv(X, I, L) => (lval(X, I -Int 1) |-> loc(L +Int I -Int 1)) getArrayEnv(X, I -Int 1, L) [owise] //requires I >Int 1

  // multiple map updates for store (used in Decl)
  syntax Map ::= Int "..." Int "|->" K [function]
  rule N...M |-> _ => .Map requires N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K requires N <=Int M




  // Chan
  syntax Msg ::= msg(List) | "noMsg"
  syntax Queue ::= queue(Int, List) // queue size , list of Msg's
  syntax Port ::= bfPort(Int) | rvPort(Int)
  syntax Value ::= Port
  syntax Stmt ::= #send(KItem, KItem) | #recv(KItem, KItem)

  // can't tell yet if its rv or async channel (may change if C [ IEXP ] contains global variables)
  rule <k> SetItem(choice(_E, (C [ IEXP ] ! EXPL => atomic { #send(C [ IEXP ], EXPL) }) ~> _K)) _:Set ...</k>
  rule <k> SetItem(choice(_E, (C [ IEXP ] ? EXPL => atomic { #recv(C [ IEXP ], EXPL) }) ~> _K)) _:Set ...</k>


    //               //
   // Buffered Send //
  //               //

  // 1) Prologue: check buffered sendable
  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         SetItem(choice(_E => sil, // init acq
           (#send(C [ IEXP ] => eval(C [ IEXP ], ENV, STR, BFC), _)) ~> _K))
         (_:Set => .Set) // choose
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool bfPort(_) :=K eval(C [ IEXP ], ENV, STR, BFC) // check port type
             andBool eval(nfull(C [ IEXP ]), ENV, STR, BFC) ==K true // buf send poll

  // 2) make msg
  rule <k> SetItem(choice(_E, (#send(bfPort(_), EXPL:Exprs => msg(evalList(EXPL, ENV, STR, BFC)))) ~> _K)) _:Set ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan>

  // 3) push msg
  rule <k> SetItem(choice(_E, (#send(bfPort(J), MSG:Msg) => .K) ~> _K)) _:Set ...</k>
       <bfChan>... J |-> queue(_SIZE, _LIST (.List => ListItem(MSG))) ...</bfChan>

    //               //
   // Buffered Recv //
  //               //

  // constraint checking function for recv
  syntax Bool ::= matchMsg(Exprs, List) [function] // pattern match EXPL := VL where MSG = msg(VL) to check recv constraints
  rule matchMsg((E , E' , EL), ListItem(V) VL) => matchMsg(E, ListItem(V)) andBool matchMsg((E' , EL), VL)
  rule matchMsg((V:Value, .Exprs), ListItem(V)) => true
  rule matchMsg((_:Vref, .Exprs), ListItem(_)) => true
  rule matchMsg(_, _) => false [owise]

  // 1) Prologue: check buffered recvable
  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         SetItem(choice(_E => sil, // init acq
           (#recv(C [ IEXP ] => eval(C [ IEXP ], ENV, STR, BFC), EXPL)) ~> _K))
         (_:Set => .Set) // choose
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool bfPort(_) :=K eval(C [ IEXP ], ENV, STR, BFC) // check port type
             andBool eval(C [ IEXP ] ?? EXPL, ENV, STR, BFC) ==K true // buf recv poll

  // 2) pop msg
   rule <k> SetItem(choice(_E, (#recv(bfPort(J), EXPL) => #assignMsg(EXPL, VL)) ~> _K)) _:Set ...</k>
       <bfChan>... J |-> queue(_SIZE, (ListItem(msg(VL)) => .List) _LIST) ...</bfChan>

  // 3) assign msg
  syntax Stmt ::= #assignMsg(Exprs, List)
  rule <k> SetItem(choice(_E, ( 
                                #assignMsg((E , E' , EL), ListItem(V) VL)
                                =>
                                (#assignMsg(E , ListItem(V)) ~> #assignMsg((E' , EL), VL))
                              ) ~> _K)) _:Set ...</k>

  rule <k> SetItem(choice(_E, ( #assignMsg((V:Value , .Exprs), ListItem(V)) => .K ) ~> _K)) _:Set ...</k>
  rule <k> SetItem(choice(_E, ( #assignMsg((X:Id , .Exprs), ListItem(V)) => (X = V):Stmt ) ~> _K)) _:Set ...</k>
  rule <k> SetItem(choice(_E, ( #assignMsg((X [ E ] , .Exprs), ListItem(V)) => (X [ E ] = V):Stmt ) ~> _K)) _:Set ...</k>



    //               //
   //  Rendez-Vous  //
  //               //
  // 1) check rendezvous - TODO: atomic effect (seems recv takes the lock)
  rule
    <proc>...
      <k> SetItem(choice(_E,  ((#send(C [ IEXP ], SEL) => .K) ~> _K))) (_:Set => .Set) ...</k>
      <env> ENV </env>
 ...</proc>
    <proc>...
      <k> SetItem(choice(_E', ((#recv(C' [ IEXP' ], REL) => #assignMsg(REL, evalList(SEL, ENV, STR, BFC))) ~> _K'))) (_:Set => .Set) ...</k>
      <env> ENV' </env>
 ...</proc>
    <store> STR </store> <bfChan> BFC </bfChan>
    requires rvPort(_) :=K eval(C [ IEXP ], ENV, STR, BFC) // check port type
             andBool eval(C [ IEXP ], ENV, STR, BFC) ==K eval(C' [ IEXP' ], ENV', STR, BFC) // check port id






  // Run - WARNING: env is NOT INHERITED!!
/*
  rule <k> run X:Id ( _EL:Exprs ) => .K ...</k> <env> ENV </env>
       <proctype>... <procName> X </procName> <procParams> _DL </procParams> <procBody> S </procBody> ...</proctype>
       <nextPid> L => L +Int 1 </nextPid>
       (.Bag => <proc>...
                  <pid> L </pid>
                  //<pName> X </pName>
                  <k> SetItem(choice(sil, S)) </k> // TODO DL = EL ~> S
                  <env> ENV </env> // inherits ENV from the parent
             ...</proc>)
*/
endmodule
