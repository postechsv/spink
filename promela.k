module PROMELA-SYNTAX
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
                     | Vref "=" Expr // Assign
                     | Vref "!" Exprs // Send
                     | Vref "?" Exprs // Recv
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
                | "run" Id "(" Exprs ")"

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

module PROMELA-CONFIG
  imports PROMELA-SYNTAX
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

module PROMELA
  imports PROMELA-CONFIG

  /****************
  BASIC DEFINITIONS
  *****************/


  syntax KItem ::= "null" | loc(Int) | lval(Id, Int)
                 | choice(Bool, K) // Acquiring Choice
                 //| guard(BasicStmt)
                 | "#rel"
                 | #assign(KItem, KItem)
                 | #expr(Expr)
                 | #run(Id, Exprs)

  // Chan
  syntax Msg ::= msg(List) | "noMsg"
  syntax Queue ::= queue(Int, List) // queue size , list of Msg's
  syntax Port ::= bfPort(Int) | rvPort(Int)
  syntax Value ::= Port
  syntax Stmt ::= #send(KItem, KItem) | #recv(KItem, KItem)


  /****************
  FUNCTION DEFINITIONS
  *****************/

  // Eval - eval : Expr, Env, Str, Bfc
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
  rule eval(E1 * E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int *Int {eval(E2, ENV, STR, BFC)}:>Int
  rule eval(E1 / E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Int /Int {eval(E2, ENV, STR, BFC)}:>Int
 
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

  // constraint checking function for recv
  syntax Bool ::= matchMsg(Exprs, List) [function] // pattern match EXPL := VL where MSG = msg(VL) to check recv constraints
  rule matchMsg((E , E' , EL), ListItem(V) VL) => matchMsg(E, ListItem(V)) andBool matchMsg((E' , EL), VL)
  rule matchMsg((V:Value, .Exprs), ListItem(V)) => true
  rule matchMsg((_:Vref, .Exprs), ListItem(_)) => true
  rule matchMsg(_, _) => false [owise]

  // Unfold basic statements
  syntax K ::= unfold(BasicStmt) [function]
  rule unfold(S) => S [owise]
  rule unfold(E:Expr) => #expr(E) ~> effect(E)
  rule unfold((X [ IE ] = E):BasicStmt) => #assign(X [ IE ], E) ~> effect(IE) ~> effect(E)

  // extract the effect from expr
  syntax K ::= effect(Expr) [function]
  rule effect(run X ( EL )) => #run(X, EL)
  rule effect(_:Value) => .K
  rule effect(_:Id) => .K
  rule effect(_[IE]) => effect(IE)
  rule effect(E1 + E2) => effect(E1) ~> effect(E2)
  rule effect(E1 - E2) => effect(E1) ~> effect(E2)
  rule effect(E1 * E2) => effect(E1) ~> effect(E2)
  rule effect(E1 / E2) => effect(E1) ~> effect(E2)
  rule effect(E1 < E2) => effect(E1) ~> effect(E2)
  rule effect(E1 <= E2) => effect(E1) ~> effect(E2)
  rule effect(E1 > E2) => effect(E1) ~> effect(E2)
  rule effect(E1 >= E2) => effect(E1) ~> effect(E2)
  rule effect(E1 == E2) => effect(E1) ~> effect(E2)
  rule effect(E1 != E2) => effect(E1) ~> effect(E2)


  // Stop for debug
  syntax Stmt ::= "stop"

  // Done
  rule <k> (SetItem ( choice ( _ , .K ) ) => .Set) ...</k>
  rule <k> (.Set:K => .K) ...</k>


  // Lift
  rule <pid> PID </pid> <lock> LCK </lock>
       <k> S:Stmt => flatten(SetItem(choice(PID ==K LCK, S))) ...</k>

  // Sequence - TODO higher priority than lift
  rule <k> (S1 ; S2):Stmt => S1 ~> S2 ...</k>


  /*******************************************************
      Flattening Rules 
  *******************************************************/

  syntax Set ::= flatten(Set) [function]

  // Decompose
  rule flatten(SetItem(C) SetItem(C') CS) => flatten(SetItem(C)) flatten(SetItem(C') CS)

  // Default
  rule flatten(CS:Set) => CS [owise]

  // Guard - protect (guarantee atomicity for multi-step flat stmts)
  // Expr, Assign, Send, Recv
  rule flatten(SetItem(choice(false, S:BasicStmt ~> K)))
    => flatten(SetItem(choice(false, atomic { S } ~> K)))

  // Guard - already protected
  rule flatten(SetItem(choice(true, S:BasicStmt ~> K)))
    => SetItem(choice(true, unfold(S) ~> K)) // this is the generic normal form

  // Sequence
  rule flatten(SetItem(choice(A, (S1 ; S2):Stmt ~> K)))
    => flatten(SetItem(choice(A, S1 ~> S2 ~> K)))

  // Select - decompose
  rule flatten(SetItem(choice(A, if (:: S) OPTL fi ~> K)))
    => flatten(SetItem(choice(A, S ~> K))) flatten(SetItem(choice(A, if OPTL fi ~> K)))

  // Select - empty
  rule flatten(SetItem(choice(_, if .Optns fi ~> _)))
    => .Set

  // Loop
  rule flatten(SetItem(choice(A, do (:: S) OPTL od ~> K)))
    => flatten(SetItem(choice(A, if (:: S) OPTL fi ~> do (:: S) OPTL od ~> K)))

  // Break - break
  rule flatten(SetItem(choice(A, break ~> do _ od ~> K)))
    => flatten(SetItem(choice(A, K)))

  // Break - propagate
  rule flatten(SetItem(choice(A, break ~> S:Stmt ~> K)))
    => flatten(SetItem(choice(A, break ~> K)))
    requires do _ od :/=K S

  // Atomic - fresh
  rule flatten(SetItem(choice(false, atomic { S } ~> K)))
    => flatten(SetItem(choice(true, S ~> #rel ~> K)))

  // Atomic - redundant (either locked or #rel inserted)
  rule flatten(SetItem(choice(true, atomic { S } ~> K)))
    => flatten(SetItem(choice(true, S ~> K)))

  /*******************************************************
      Collapse Rules 
  *******************************************************/
  // Assign
  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         ((SetItem(choice(true, #assign(X [ IE ], EXP) ~> BK)) _:Set) => .Set) // choose
       ~> (.K => (#assign(lval(X, {eval(IE, ENV, STR, BFC)}:>Int), eval(EXP, ENV, STR, BFC)) ~> BK))
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan>  
    requires (LCK ==K #none orBool LCK ==K PID) // check lock



  /*******************************************************
      Effect Rules 
  *******************************************************/
  // Assign
  // Assign-a) non-channel assignment
  rule <k> #assign(lval(X, I), V:Value) => .K ...</k>
       <env>... lval(X, I) |-> loc(L) ...</env>
       <store>... L |-> (_ => V) ...</store>

  // Assign-b) channel assignment
  rule <k> #assign(lval(X, I), V:Port) => .K ...</k>
       <env>... lval(X, I) |-> (_:Port => V) ...</env>



/* OLD
  // Rel
  rule <k> 
         SetItem(choice(_, (#rel => .K) ~> _K))
         _:Set // this may not be necessary
    ...</k>
       <lock> _ => #none </lock>

*/

  /*******************************************************
        BASIC ACTIONS (BasicStmt)
  *******************************************************/

  rule (X:Id = V):Stmt => (X [ 0 ] = V):Stmt // desugar



/* OLD
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

  // assign - new version
  syntax Stmt ::= #assign(KItem, KItem)

  rule <k> SetItem(choice(_E, ((X [ IE ] = E):Stmt => atomic { #assign(X [ IE ], E) }) ~> _K)) _:Set ...</k>

  // 1) Prologue : identification
  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         SetItem(choice(_EFF => sil, // init acq
           #assign(X [ IE ] => lval(X, {eval(IE, ENV, STR, BFC)}:>Int), EXP => eval(EXP, ENV, STR, BFC)) ~> _K))
         (_:Set => .Set) // choose
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan>  
    requires (LCK ==K #none orBool LCK ==K PID) // check lock

  // 2-a) non-channel assignment
  rule <k> SetItem(choice(_E, (#assign(lval(X, I), V:Value) => .K) ~> _K)) _:Set ...</k>
       <env>... lval(X, I) |-> loc(L) ...</env>
       <store>... L |-> (_ => V) ...</store>

  // 2-b) channel assignment
  rule <k> SetItem(choice(_E, (#assign(lval(X, I), V:Port) => .K) ~> _K)) _:Set ...</k>
       <env>... lval(X, I) |-> (_:Port => V) ...</env>

  

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

*/




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
