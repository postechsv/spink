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

  syntax Decls ::= List{Decl, ";"} // this often causes ambiguity w/ Seq

  syntax Type ::= "int" | "bool" | "chan"

  syntax Types ::= List{Type, ","}

  syntax BasicStmt ::= Decl | Expr
                     | Vref "=" Expr // Assign
                     | Vref "!" Exprs // Send
                     | Vref "?" Exprs // Recv
                     | "skip"

  syntax Goto ::= "goto" Id | "break"

  syntax Stmt ::= BasicStmt
                | Goto
                | "atomic" "{" Stmt "}"
                | "if" Optns "fi"
                | "do" Optns "od"

  syntax Seq ::= List{Stmt, ";"}

  syntax Expr ::= Const | Vref
                | "(" Expr ")" [bracket]
                | "-" Expr | "!" Expr
                | Expr "+" Expr | Expr "-" Expr | Expr "*" Expr | Expr "/" Expr 
                | Expr "<" Expr | Expr "<=" Expr | Expr ">" Expr | Expr ">=" Expr 
                | Expr "&&" Expr | Expr "||" Expr | Expr "==" Expr | Expr "!=" Expr 
                | full(Vref) | empty(Vref) | nfull(Vref) | nempty(Vref)
                | Vref "?" "[" Exprs "]" // Recv Poll (only for buf chans)
                | "run" Id "(" Exprs ")"

  syntax Exprs ::= List{Expr, ","}

  syntax Optn ::= "::" Seq

  syntax Optns ::= List{Optn, ""}

  syntax Ivar ::= Ivar "," Ivar | Vref
                | Vref "=" Expr
                | Vref "=" "[" Const "]" "of" "{" Types "}"

  syntax Vref ::= Id | Id "[" Expr "]"

  syntax Const ::= Value

  syntax Value ::= Int | Bool
endmodule

module BASIC
  imports MINIMELA-SYNTAX
  imports DOMAINS

  syntax Value ::= Chan

  syntax Chan ::= ch(Int) | hs(Int) // ch_id as a value // the name chan is already reserved for typename
  syntax Loc ::= loc(Int)

  syntax Queue ::= mq(Int, List) // capacity, list of messages
  syntax Msg ::= m(List) // list of values
               | "noMsg"

  syntax Lock ::= Int | "#none"

  syntax KItem ::= "null"
                 | lval(Id, Int) // vref

  syntax Ref ::= Vref | Chan | Loc
endmodule

module CONFIG
  imports BASIC
  imports SET

  syntax Id ::= "$procName" [token]

  configuration <T color="yellow">
                  /* PROCTYPES */
                  <proctypes>
                    <proctype multiplicity="*" type="Map" initial="">
                      <procName> $procName </procName>
                      <procParams> .Decls </procParams>
                      <procBody> skip:Stmt </procBody> // skip:BasicStmt doesn't allow Stmt's in general
                      <gotoMap> .Map </gotoMap>
                    </proctype>
                  </proctypes>

                  /* PROCS */
                  <procs>
                    <proc multiplicity="*" type="Map" color="orange" initial="">
                      <pid> -1 </pid>
                      <name> $procName </name>
                      <k color="green"> $PGM:Spec </k>
                      <local color="orange"> .Set </local>
                      <env color="orange"> .Map </env>
                    </proc>
                  </procs> 

                  <store color="Salmon"> .Map </store>
                  <network color="Salmon"> .Map </network>

                  <lock> #none </lock>

                  <nextLoc> 0 </nextLoc>
                  <nextPid> 0 </nextPid>

                </T>
endmodule

module EXPRESSION
  imports BASIC

  // Eval - eval : Exp, Env, Str, Net
  syntax Value ::= eval(Expr, Map, Map, Map) [function]

  // Lookup Expressions
  rule eval(V:Value, _, _, _) => V
  rule eval(X:Id, ENV, STR, NET) => eval(X[0], ENV, STR, NET) // desugar
  rule eval(X[EXP], ENV, STR, NET) => eval(X [ eval(EXP, ENV, STR, NET) ], ENV, STR, NET) [owise] // i.e. IEXP not Int
  rule eval(X[I:Int], (lval(X, I) |-> loc(L)) _ENV, (L |-> V) _STR, _NET) => V // loc
  rule eval(X[I:Int], (lval(X, I) |-> C:Chan) _ENV, _STR, _NET) => C // ch

  // Arith & Logic Expressions
  rule eval(E1 == E2, ENV, STR, NET) => eval(E1, ENV, STR, NET) ==K eval(E2, ENV, STR, NET)
  rule eval(E1 != E2, ENV, STR, NET) => eval(E1, ENV, STR, NET) =/=K eval(E2, ENV, STR, NET)
  rule eval(E1 + E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int +Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 - E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int -Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 * E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int *Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 / E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int /Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 && E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Bool andBool {eval(E2, ENV, STR, NET)}:>Bool
  rule eval(E1 || E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Bool orBool {eval(E2, ENV, STR, NET)}:>Bool
  rule eval(E1 < E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int <Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 <= E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int <=Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 > E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int >Int {eval(E2, ENV, STR, NET)}:>Int
  rule eval(E1 >= E2, ENV, STR, NET) => {eval(E1, ENV, STR, NET)}:>Int >=Int {eval(E2, ENV, STR, NET)}:>Int

  // Poll Expressions
  rule eval(full(X [ EXP ]), ENV, STR, NET) => eval(full(X [ eval(EXP, ENV, STR, NET) ]), ENV, STR, NET) requires _:Int :/=K EXP
  rule eval(empty(X [ EXP ]), ENV, STR, NET) => eval(empty(X [ eval(EXP, ENV, STR, NET) ]), ENV, STR, NET) requires _:Int :/=K EXP
  rule eval(nfull(X [ EXP ]), ENV, STR, NET) => eval(nfull(X [ eval(EXP, ENV, STR, NET) ]), ENV, STR, NET) requires _:Int :/=K EXP
  rule eval(nempty(X [ EXP ]), ENV, STR, NET) => eval(nempty(X [ eval(EXP, ENV, STR, NET) ]), ENV, STR, NET) requires _:Int :/=K EXP

  rule eval(full(X [ I:Int ]), (lval(X, I) |-> ch(C)) _ENV, _STR, (C |-> mq(S, Q)) _NET) => size(Q) ==Int S
  rule eval(empty(X [ I:Int ]), (lval(X, I) |-> ch(C)) _ENV, _STR, (C |-> mq(_S, Q)) _NET) => size(Q) ==Int 0
  rule eval(nfull(X [ I:Int ]), (lval(X, I) |-> ch(C)) _ENV, _STR, (C |-> mq(S, Q)) _NET) => size(Q) <Int S
  rule eval(nempty(X [ I:Int ]), (lval(X, I) |-> ch(C)) _ENV, _STR, (C |-> mq(_S, Q)) _NET) => size(Q) >Int 0

  rule eval(full(_ [ _:Int ]), _ENV, _STR, _NET) => false [owise]
  rule eval(empty(_ [ _:Int ]), _ENV, _STR, _NET) => false [owise]
  rule eval(nfull(_ [ _:Int ]), _ENV, _STR, _NET) => false [owise]
  rule eval(nempty(_ [ _:Int ]), _ENV, _STR, _NET) => false [owise]
 
  rule eval(C [ I:Int ] ? [ EXPL ], (lval(C, I) |-> ch(J)) _ENV, _STR, (J |-> mq(_, ListItem(m(VL)) _Q)) _NET)
    => true requires matchMsg(EXPL, VL)
//  rule eval(_ [ _:Int ] ? _, _ENV, _STR, _NET) => false [owise]


  // evalList - FIXME eval with brackets e.g. c ! (1 + 1) , (1 + 2) doesn't work
  //rule eval(( E:Expr ), ENV, STR, NET) => eval(E, ENV, STR, NET)
  syntax List ::= evalList(Exprs, Map, Map, Map) [function]
  rule evalList((E , E' , EL), ENV, STR, NET) => ListItem(eval(E, ENV, STR, NET)) evalList((E', EL), ENV, STR, NET)
  rule evalList((E , .Exprs), ENV, STR, NET) => ListItem(eval(E, ENV, STR, NET))

  // constraint checking function for recv
  syntax Bool ::= matchMsg(Exprs, List) [function] // pattern match EXPL := VL where MSG = msg(VL) to check recv constraints
  rule matchMsg((E , E' , EL), ListItem(V) VL) => matchMsg(E, ListItem(V)) andBool matchMsg((E' , EL), VL)
  rule matchMsg((V:Value, .Exprs), ListItem(V)) => true
  rule matchMsg((_:Vref, .Exprs), ListItem(_)) => true
  rule matchMsg(_, _) => false [owise]

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
endmodule


module ATOMICITY
  imports CONFIG

  syntax KItem ::= "#rel"

  // Release (Controlled)
  rule <k> #rel => .K ...</k> <pid> PID </pid>
       <lock> PID => #none </lock> // acquire

  // Loose (Uncontrolled)
  rule <lock> _:Int => #none </lock> [owise]
endmodule


module GOTO
  imports CONFIG

  syntax KItem ::= gotoCtx(Bool, K) // Bool indicates wherether K is in an atomic block

  // goto
  rule <lock> _LCK => #if B #then PID #else #none #fi </lock>
       <pid> PID </pid> // acquire
       <name> P </name>
       <k> (goto L ~> _) => K </k>
       <proctype>...
         <procName> P </procName>
         <gotoMap>... L |-> gotoCtx(B, K) ...</gotoMap>
    ...</proctype> 

  // break
  rule (break ~> do _ od) => .K
  rule break ~> (KI:KItem => .K) requires do _ od :/=K KI
endmodule


module ASSIGN
  imports CONFIG
  imports EXPRESSION
  syntax KItem ::= #assign(Id, Expr, Expr)

  // Evaluate Index
  rule <k> #assign(_, E => {eval(E, ENV, STR, NET)}:>Int, _) ...</k>
       <env> ENV </env> <store> STR </store> <network> NET </network> 
    requires _:Int :/=K E

  // Evaluate Expr
  rule <k> #assign(_, _:Int, E => eval(E, ENV, STR, NET)) ...</k>
       <env> ENV </env> <store> STR </store> <network> NET </network> 
    requires _:Value :/=K E

  // Ordinary Assignment
  rule <k> #assign(X, I:Int, V:Value) => .K ...</k>
       <env>... lval(X, I) |-> loc(L) ...</env>
       <store>... L |-> (_ => V) ...</store>

  // Channel Assignment
  rule <k> #assign(X, I:Int, V:Chan) => .K ...</k>
       <env>... lval(X, I) |-> (_ => V) ...</env>
endmodule


module CHANNEL
  imports CONFIG
  imports EXPRESSION
  imports ASSIGN

  syntax KItem ::= #send(Ref, Exprs)
                 | #sendMsg(Chan, Msg)
                 | #recv(Ref, Exprs)
                 | #recvMsg(Exprs, Msg)

  /* Buffered Send */

  // Identify Chan
  rule <k> #send(X [ E ] => {eval(X [ E ], ENV, STR, NET)}:>Chan, _) ...</k>
       <env> ENV </env> <store> STR </store> <network> NET </network>

  // Make Msg
  rule <k> #send(ch(I), EL) => #sendMsg(ch(I), m(evalList(EL, ENV, STR, NET)))...</k>
       <env> ENV </env> <store> STR </store> <network> NET </network>

  // Push Msg
  rule <k> #sendMsg(ch(I), MSG) ...</k>
       <network>... I |-> mq(_, _LIST(.List => ListItem(MSG))) ...</network>

  /* Buffered Recv */ 
  // Identify Chan
  rule <k> #recv(X [ E ] => {eval(X [ E ], ENV, STR, NET)}:>Chan, _) ...</k>
       <env> ENV </env> <store> STR </store> <network> NET </network>

  // Pop Msg
  rule <k> #recv(ch(I), EL) => #recvMsg(EL, MSG) ...</k>
       <network>... I |-> mq(_, (ListItem(MSG) => .List) _LIST) ...</network>

  // Assign Msg
  rule #recvMsg(.Exprs, _) => .K
  rule #recvMsg((V:Value , EL), m(ListItem(V) VL)) => #recvMsg(EL, m(VL))
  rule #recvMsg((X [ E ] , EL), m(ListItem(V) VL)) => #assign(X, E, V) ~> #recvMsg(EL, m(VL))
  rule #recvMsg((X:Id , EL), m(ListItem(V) VL)) => #assign(X, 0, V) ~> #recvMsg(EL, m(VL))

endmodule


module RUN
  imports CONFIG

  syntax Map ::= gEnv(Map, Set) [function] // remove local variables from ENV
  rule gEnv((lval(X:Id, _) |-> _) M, SetItem(X) S) => gEnv(M, SetItem(X) S)
  rule gEnv(M, _) => M [owise]

  syntax KItem ::= #run(Id, Exprs)
  //
  rule <procs>...
         <proc>...
           <k> #run(P, _EL) => .K ...</k>
           <local> IDS </local>
           <env> ENV </env>
      ...</proc>
         (.Bag =>
         <proc>
           <pid> PID </pid>
           <name> P </name>
           <k> S </k> // FIXME: param init
           <local> .Set </local>
           <env> gEnv(ENV, IDS) </env>
         </proc>)
    ...</procs>

       <proctype>...
         <procName> P </procName>
         //<procParams>  <procParams>
         <procBody> S </procBody>
    ...</proctype>

       <nextPid> PID </nextPid>
endmodule


module GUARD // BASICSTMT
/*
  purification must be done while Basic Decomposition, i.e. before any run is done
*/
  imports EXPRESSION
  imports ASSIGN
  imports CHANNEL
  imports RUN

  /* Executability Condition Test */
  syntax Bool ::= isExec(BasicStmt, Map, Map, Map, Int) [function]
  rule isExec(_, _, _, _, _) => false [owise]
  rule isExec(E:Expr, ENV, STR, NET, PID)
    => {eval(purify(E, PID), ENV, STR, NET)}:>Bool ==K true
       // FIXME: orBool {eval(purify(E, PID), ENV, STR, NET)}:>Int >Int 0 // Condition
  rule isExec(_ = _, _, _, _, _) => true // Assign
  rule isExec(X [ E ] ! _, ENV, STR, NET, _)
    => eval(nfull(X [ E ]), ENV, STR, NET) ==K true // Buf Send
  rule isExec(X [ E ] ? EL, ENV, STR, NET, _)
    => eval(X [ E ] ? [ EL ], ENV, STR, NET) ==K true // Buf Recv


  /* Basic-Effect Decomposition */  
  syntax K ::= effect(BasicStmt, Int) [function]
  rule effect(_, _) => .K [owise]
  // Run Effects
  rule effect(run X ( EL ), _) => #run(X, EL)
  rule effect(E1 + E2, PID)    => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 - E2, PID)    => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 * E2, PID)    => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 / E2, PID)    => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 && E2, PID)   => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 || E2, PID)   => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 < E2, PID)    => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 <= E2, PID)   => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 > E2, PID)    => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 >= E2, PID)   => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 == E2, PID)   => effect(E1, PID) ~> effect(E2, PID)
  rule effect(E1 != E2, PID)   => effect(E1, PID) ~> effect(E2, PID)
  // Basic Effects
  rule effect(X = E, PID) => #assign(X, 0, purify(E, PID))
  rule effect(X [ E ] = E', PID) => effect(E', PID) ~> #assign(X, E, purify(E', PID))
  rule effect(X [ E ] ! EL, _) => #send(X [ E ], EL)
  rule effect(X [ E ] ? EL, _) => #recv(X [ E ], EL)
endmodule


module CONTROL // CONTROL-DECOMPOSITION or CONTROL-EFFECT as opposed GUARD-EFFECT
/*
  control effects are applied functionally, with "des"
*/
  imports BASIC
  imports ATOMICITY

  syntax KItem ::= "@[" K "]" // stores branch as a local computation K

  /* Control-Effect Decomposition */
  syntax Set ::= des(Bool, K) [function] // des(true, ...) means #rel is inserted appropriately
  rule des(true, BS:BasicStmt ~> K) => SetItem(@[ BS ~> K ])
  rule des(false, BS:BasicStmt ~> K) => des(true, BS ~> #rel ~> K)
  rule des(B, (S ; S'):Seq ~> K) => des(B, S ~> S' ~> K) // FIXME
  rule des(true, atomic { S } ~> K) => des(true, S ~> K) // inner atomic
  rule des(false, atomic { S } ~> K) => des(true, S ~> #rel ~> K) // outermost atomic
  rule des(B, if (:: S) OL fi ~> K) => des(B, S ~> K) des(B, if OL fi ~> K)
  rule des(_, if .Optns fi ~> _) => .Set
  rule des(B, S:Goto ~> K) => des(B, true ~> S ~> K)
//  rule des(B, goto L ~> K) => des(B, true ~> goto L ~> K)
  rule des(B, do OL od ~> K) =>  des(B, if OL fi ~> do OL od ~> K)
//  rule des(B, break ~> K) => des(B, true ~> break ~> K)
  rule des(_, K) => K [owise]
endmodule


module MINIMELA
  imports CONFIG
  imports EXPRESSION
  imports CONTROL
  imports GUARD
  imports GOTO

  syntax Stmt ::= "stop"

/* this does not work
  // Sequential Decomposition
  rule <pid> PID </pid> <lock> LCK </lock>
       <k> (S1:Stmt ; S2:Stmt ; S) => S1 ~> (S2 ; S):Seq ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock

  rule <pid> PID </pid> <lock> LCK </lock>
       <k> (S:Stmt ; .Seq) => S:Stmt ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
  // seems because in the rhs of the second rule,
     S is implicitly transformed into S ; .Seq,
     becase lhs is of type Seq
*/

 // Sequential Decomposition
  rule <pid> PID </pid> <lock> LCK </lock>
       <k> (S ; S'):Seq => S ~> S' ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock

  rule <pid> PID </pid> <lock> LCK </lock>
       <k> .Seq => .K ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock

  // Control Decomposition
  rule <pid> PID </pid> <lock> LCK </lock>
       <k> S:Stmt => des(PID ==K LCK, S) ...</k>
    requires (_:Goto :/=K S)
             andBool (LCK ==K #none orBool LCK ==K PID) // check lock

  // Basic Decomposition
  rule <k> (SetItem(@[BS ~> K]) _:Set) => (effect(BS, PID') ~> K) ...</k>
       <pid> PID </pid>
       <env> ENV </env>
       <store> STR </store>
       <network> NET </network>
       <nextPid> PID' </nextPid>
       <lock> LCK => PID </lock> // acquire
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool isExec(BS, ENV, STR, NET, PID') ==K true

  /* Handshake */
  syntax KItem ::= #toss(Lock) // generalizes #rel (i.e. #rel = #toss(#none))
  rule <k> #toss(LCK) ...</k> <lock> _ => LCK </lock>

  // @[K2] becase K2 might contain #rel; but what if goto is in the front
  rule
    <proc>...
      <pid> PID1 </pid>
      <k>
        (SetItem(@[ X1 [ E1 ] ! EL1 ~> K1 ]) _) => des(true, K1)
   ...</k>
      <env> ENV1 </env>
 ...</proc>
    <proc>...
      <pid> PID2 </pid>
      <k>
        (SetItem(@[ X2 [ E2 ] ? EL2 ~> K2 ]) _) =>
        (#recvMsg(EL2, m(evalList(EL1, ENV, STR, NET))) ~> #toss(LCK) ~> des(true, K2))
   ...</k>
      <env> ENV2 </env>
 ...</proc>
    <lock> LCK => PID2 </lock>
    <store> STR </store>
    <network> NET </network>
    requires (LCK ==K #none orBool LCK ==K PID1 orBool LCK ==K PID2)
             andBool hs(_) :=K eval(X1 [ E1 ], ENV, STR, NET) // check if hs
             andBool eval(X1 [ E1 ], ENV1, STR, NET) ==K eval(X2 [ E2 ], ENV2, STR, NET) // check ch_id
endmodule
