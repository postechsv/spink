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

  syntax BasicStmt ::= Decl | Expr
                     | Vref "=" Expr // Assign
                     | Vref "!" Exprs // Send
                     | Vref "?" Exprs // Recv
                     | "skip"
                     | "break"
                     | "goto" Id

  syntax Stmt ::= BasicStmt | Stmt ";" | Stmt ";" Stmt [left, prefer]
                | "atomic" "{" Stmt "}"
                | "if" Optns "fi" | "do" Optns "od"

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
                  <proctypes>
                    <proctype multiplicity="*" type="Map" initial="">
                      <procName> #Configurator </procName>
                      <procParams> .Decls </procParams>
                      <procBody> skip:Stmt </procBody> // skip:BasicStmt doesn't allow Stmt's in general
                      <gotoMap> .Map </gotoMap>
                    </proctype>
                  </proctypes>

                  <procs> // active procs
                    <proc multiplicity="*" type="Map" color="orange" initial="">
                      <pid> -1 </pid>
                      <name> #Configurator </name>
                      <k color="green"> $PGM:Spec </k>
                      <env color="LightSalmon"> .Map </env>
                    </proc>
                  </procs> 

                  <store color="Salmon"> .Map </store>
                  <bfChan color="Salmon"> .Map </bfChan>

                  <lock> #none </lock>

                  <nextLoc> 0 </nextLoc>
                  <nextPid> 0 </nextPid>

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
  syntax KItem ::= #send(KItem, KItem) | #recv(KItem, KItem)


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

  rule eval(E1 && E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Bool andBool {eval(E2, ENV, STR, BFC)}:>Bool
  rule eval(E1 || E2, ENV, STR, BFC) => {eval(E1, ENV, STR, BFC)}:>Bool orBool {eval(E2, ENV, STR, BFC)}:>Bool
 
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
/*
  syntax K ::= unfold(BasicStmt) [function]
  rule unfold(S) => S [owise]
  rule unfold(E:Expr) => #expr(E) ~> effect(E)
  rule unfold((X [ IE ] = E):BasicStmt) => #assign(X [ IE ], E) ~> effect(IE) ~> effect(E)
*/

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
  rule effect(E1 && E2) => effect(E1) ~> effect(E2)
  rule effect(E1 || E2) => effect(E1) ~> effect(E2)
  rule effect(E1 < E2) => effect(E1) ~> effect(E2)
  rule effect(E1 <= E2) => effect(E1) ~> effect(E2)
  rule effect(E1 > E2) => effect(E1) ~> effect(E2)
  rule effect(E1 >= E2) => effect(E1) ~> effect(E2)
  rule effect(E1 == E2) => effect(E1) ~> effect(E2)
  rule effect(E1 != E2) => effect(E1) ~> effect(E2)

  // Purify - eliminate run operators in expr, given nextPid
  // Assume Expr can only cantain at most 1 run op (according to the manual)
  syntax Expr ::= purify(Expr, Int) [function]
  rule purify(run _ ( _ ), PID) => PID
  rule purify(V:Value, _) => V
  rule purify(X:Id, _) => X
  rule purify(X [ IE ], PID) => (X[purify(IE, PID):Expr]):Vref
  rule purify(E1 + E2, PID) => purify(E1, PID) + purify(E2, PID)
  rule purify(E1 - E2, PID) => purify(E1, PID) - purify(E2, PID)
  rule purify(E1 * E2, PID) => purify(E1, PID) * purify(E2, PID)
  rule purify(E1 / E2, PID) => purify(E1, PID) / purify(E2, PID)
  rule purify(E1 && E2, PID) => purify(E1, PID) && purify(E2, PID)
  rule purify(E1 || E2, PID) => purify(E1, PID) || purify(E2, PID)
  rule purify(E1 < E2, PID) => purify(E1, PID) < purify(E2, PID)
  rule purify(E1 <= E2, PID) => purify(E1, PID) <= purify(E2, PID)
  rule purify(E1 > E2, PID) => purify(E1, PID) > purify(E2, PID)
  rule purify(E1 >= E2, PID) => purify(E1, PID) >= purify(E2, PID)
  rule purify(E1 == E2, PID) => purify(E1, PID) == purify(E2, PID)
  rule purify(E1 != E2, PID) => purify(E1, PID) != purify(E2, PID)


  // Stop for debug
  syntax Stmt ::= "stop"

  // Done
//  rule <k> (SetItem ( choice ( _ , .K ) ) => .Set) ...</k>


  rule <pid> PID </pid> <lock> LCK </lock>
       <k> (.Set:K => .K) ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock

  // Lift & Decompose
  rule <pid> PID </pid> <lock> LCK </lock>
       <k> S:Stmt => flatten(SetItem(choice(PID ==K LCK, S))) ...</k>
    requires (goto _ :/=K S) andBool ((_ ; _):Stmt :/=K S)
             andBool (LCK ==K #none orBool LCK ==K PID) // check lock
    [owise]

  // Sequence
  rule <pid> PID </pid> <lock> LCK </lock>
       <k> (S1 ; S2):Stmt => S1 ~> S2 ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock

  /*******************************************************
      Flattening Rules 
  *******************************************************/

  syntax Set ::= flatten(Set) [function]

  // Decompose
  rule flatten(SetItem(C) SetItem(C') CS) => flatten(SetItem(C)) flatten(SetItem(C') CS)

  // Default
  rule flatten(CS:Set) => CS [owise]

  // Guard - protect (guarantee atomicity for multi-step flat stmts)
  // Expr, Assign, Send, Recv (multi-step stmts)
  rule flatten(SetItem(choice(false, S:BasicStmt ~> K)))
    => flatten(SetItem(choice(false, atomic { S } ~> K)))
   // requires S is not goto or break // these should be preceded by skip(true) via preprocessing

  // Guard - already protected
  rule flatten(SetItem(choice(true, S:BasicStmt ~> K)))
    => SetItem(choice(true, S ~> K)) // this is the generic normal form
    //=> SetItem(choice(true, unfold(S) ~> K)) // this is the generic normal form

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

  // Atomic - fresh
  rule flatten(SetItem(choice(false, atomic { S } ~> K)))
    => flatten(SetItem(choice(true, S ~> #rel ~> K)))

  // Atomic - redundant (either locked or #rel inserted)
  rule flatten(SetItem(choice(true, atomic { S } ~> K)))
    => flatten(SetItem(choice(true, S ~> K)))

  /*******************************************************
      Expr
  *******************************************************/
  // Expr - Guard
  rule <lock> LCK => PID </lock>
       <pid> PID </pid> // acquire
       <k>
         ((SetItem(choice(true, EXP:Expr ~> BK)) _:Set) => .Set) // choose
       ~> (.K => (effect(EXP) ~> BK))
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan> <nextPid> NP </nextPid>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool eval(purify(EXP, NP), ENV, STR, BFC) ==K true
             // andBool numRuns(EXP) <= 255

  /*******************************************************
     Assign 
  *******************************************************/
  // Assign - Guard
  rule <lock> LCK => PID </lock>
       <pid> PID </pid> // acquire
       <k>
         ((SetItem(choice(true, (X [ IE ] = EXP):Stmt ~> BK)) _:Set) => .Set) // choose
       ~> (.K => (#assign(X [ IE ], EXP) ~> BK))
    ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             // andBool numRuns(IE) + numRuns(EXP) <= 255

  // Assign - eval index with side-effects
  rule <k> (.K => effect(IE)) ~> #assign(X [ IE ] => lval(X, {eval(purify(IE ,NP), ENV, STR, BFC)}:>Int), _) ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan> <nextPid> NP </nextPid>

  // Assign - eval expr with side-effects
  rule <k> (.K => effect(EXP)) ~> #assign(lval(_,_), EXP => eval(purify(EXP, NP), ENV, STR, BFC)) ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan> <nextPid> NP </nextPid>
    requires _:Value :/=K EXP

  // Assign-a) non-channel assignment
  rule <k> #assign(lval(X, I), V:Value) => .K ...</k>
       <env>... lval(X, I) |-> loc(L) ...</env>
       <store>... L |-> (_ => V) ...</store>

  // Assign-b) channel assignment
  rule <k> #assign(lval(X, I), V:Port) => .K ...</k>
       <env>... lval(X, I) |-> (_:Port => V) ...</env>

  /*******************************************************
     Channel 
  *******************************************************/

  // Buffered Send
  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         ((SetItem(choice(true, C [ IE ] ! EXPL ~> BK)) _:Set) => .Set) // choose
         ~> (.K => (effect(IE) ~> #send(eval(C [ purify(IE, NP) ], ENV, STR, BFC), EXPL) ~> BK))
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan> <nextPid> NP </nextPid>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool bfPort(_) :=K eval(C [ purify(IE, NP) ], ENV, STR, BFC) // check port type
             andBool eval(nfull(C [ purify(IE, NP) ]), ENV, STR, BFC) ==K true // buf send poll

  // 2) make msg
  rule <k> #send(bfPort(_), EXPL:Exprs => msg(evalList(EXPL, ENV, STR, BFC))) ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan>

  // 3) push msg
  rule <k> #send(bfPort(J), MSG:Msg) => .K ...</k>
       <bfChan>... J |-> queue(_SIZE, _LIST (.List => ListItem(MSG))) ...</bfChan>

  // Buffered Recv
  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         ((SetItem(choice(true, C [ IE ] ? EXPL ~> BK)) _:Set) => .Set) // choose
         ~> (.K => (effect(IE) ~> #recv(eval(C [ purify(IE, NP) ], ENV, STR, BFC), EXPL) ~> BK))
    ...</k>
       <env> ENV </env> <store> STR </store> <bfChan> BFC </bfChan> <nextPid> NP </nextPid>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool bfPort(_) :=K eval(C [ purify(IE, NP) ], ENV, STR, BFC) // check port type
             andBool eval(C [ purify(IE, NP) ] ?? EXPL, ENV, STR, BFC) ==K true // buf recv poll

  // Recv - 2) pop msg
   rule <k> #recv(bfPort(J), EXPL) => #assignMsg(EXPL, VL) ...</k>
        <bfChan>... J |-> queue(_SIZE, (ListItem(msg(VL)) => .List) _LIST) ...</bfChan>

  // Recv - 3) assign msg
  syntax KItem ::= #assignMsg(Exprs, List)
  rule <k> #assignMsg((E , E' , EL), ListItem(V) VL)
           => (#assignMsg(E , ListItem(V)) ~> #assignMsg((E' , EL), VL))
    ...</k>
  rule <k> #assignMsg((V:Value , .Exprs), ListItem(V)) => .K ...</k>
  rule <k> #assignMsg((X:Id , .Exprs), ListItem(V)) => #assign(X [ 0 ], V) ...</k>
  rule <k> #assignMsg((X [ IE ] , .Exprs), ListItem(V)) => #assign(X [ IE ], V) ...</k>

  // TODO: Rendez-Vous
  // 1) check rendezvous - TODO: atomic effect (seems recv takes the lock)
  // TODO atomicity pass: search 'global atomic chain of executions' in https://spinroot.com/spin/Man/atomic.html
/*
  rule
    <proc>...
      <pid> SID </pid>
      <k>
        ((SetItem(choice(true,  (SC [ SIE ] ! SEL ~> SBK))) _:Set) => .Set)
        ~> (.K => SBK)
   ...</k>
      <env> ENV </env>
 ...</proc>
    <proc>...
      <pid> RID </pid>
      <k>
        ((SetItem(choice(true, (RC [ RIE ] ? REL ~> RBK))) _:Set) => .Set)
        ~> (.K => #assignMsg(REL, evalList(SEL, ENV, STR, BFC)))
   ...</k>
      <env> ENV' </env>
 ...</proc>
    <lock> LCK </lock>
    <store> STR </store> <bfChan> BFC </bfChan>
    requires (LCK ==K #none orBool LCK ==K SID orBool LCK ==K RID)
             andBool rvPort(_) :=K eval(C [ IEXP ], ENV, STR, BFC) // check port type
             andBool eval(C [ IEXP ], ENV, STR, BFC) ==K eval(C' [ IEXP' ], ENV', STR, BFC) // check port id
*/


  /*******************************************************
      Atomic 
  *******************************************************/

  rule <lock> PID => #none </lock> <pid> PID </pid> // acquire
       <k> #rel => .K ...</k>

  /*******************************************************
      Loop
  *******************************************************/
  // break
/*
  syntax KItem ::= "#break"

  rule <lock> LCK => PID </lock> <pid> PID </pid> // acquire
       <k>
         ((SetItem(choice(true, break ~> BK)) _:Set) => .Set) // choose
       ~> (.K => (#break ~> BK))
    ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
*/
  /*******************************************************
      Goto
  *******************************************************/

  rule <lock> _LCK => #if B #then PID #else #none #fi </lock>
       <pid> PID </pid> // acquire
       <name> P </name>
       <k> (goto L ~> _) => K </k>
       <proctype>...
         <procName> P </procName>
         <gotoMap>... L |-> choice(B, K) ...</gotoMap> // TODO rename choice as e.g. K w/ atomic ctx
    ...</proctype> 

  /*******************************************************
        BASIC ACTIONS (BasicStmt)
  *******************************************************/

//  rule (X:Id = V):Stmt => (X [ 0 ] = V):Stmt // desugar



endmodule
