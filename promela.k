module PROMELA-SYNTAX
  imports DOMAINS-SYNTAX

  //syntax Spec ::= List{Mdle, " "}

  syntax Spec ::= Proc
                | Decl
                | Spec Spec [left]

  syntax Proc ::=  Active "proctype" Id "(" Decls ")" "{" Seq "}"
                 | "proctype" Id "(" Decls ")" "{" Seq "}"

  syntax Active ::= "active" | "active" "[" Const "]"

  syntax Decl ::= Type Ivar
  syntax Decls ::= List{Decl, ";"} // this often causes ambiguity w/ Seq


  syntax PType ::= "int" | "bool" 
  syntax CType ::= "chan"
  syntax Type ::= PType | CType
  syntax Types ::= List{Type, ","}

  syntax BasicStmt ::= Decl | Expr
                     | Vref "=" Expr [prefer] // Assign
                     | Vref "!" Exprs // Send
                     | Vref "?" Exprs // Recv
                     | "skip"
  syntax GotoStmt ::= "goto" Id | "break"
  syntax DeclStmt ::= Decl // originally corresponds to decl "step"
  syntax Stmt ::= BasicStmt
                | DeclStmt
                | GotoStmt
                | "atomic" "{" Seq "}"
                | "if" Optns "fi"
                | "do" Optns "od"

  syntax Seq ::= List{Stmt, ";"} [prefer]

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
  imports PROMELA-SYNTAX
  imports DOMAINS

  syntax Value ::= Chan

  syntax Chan ::= ch(Int) | hs(Int) // ch_id as a value // the name chan is already reserved for typename
  syntax Loc ::= loc(Int)

  syntax Queue ::= mq(Int, List) // capacity, list of messages
  syntax Msg ::= m(List) // list of values
               | "noMsg"

  syntax Lock ::= Int | "#none" | "#frozen" // frozen is added for #freeze

  syntax KItem ::= "null"
                 | lval(Id, Int) // vref

  syntax Ref ::= Vref | Chan | Loc
endmodule

module CONFIG
  imports BASIC
  imports SET

  syntax Id ::= "Main" [token]

  configuration <T color="yellow">
                  /* PROCTYPES */
                  <proctypes>
                    <proctype multiplicity="*" type="Map" initial="">
                      <procName> Main </procName>
                      <procParams> .Decls </procParams>
                      <procBody> .K </procBody> // skip:BasicStmt doesn't allow Stmt's in general
                      <gotoMap> .Map </gotoMap>
                    </proctype>
                  </proctypes>

                  /* PROCS */
                  <procs>
                    <proc multiplicity="*" type="Map" color="orange" initial="">
                      <pid> -1 </pid>
                      <name> Main </name>
                      <k color="green"> $PGM:Spec </k>
                      <local color="orange"> .Set </local>
                      <env color="orange"> .Map </env>
                    </proc>
                  </procs> 

                  <store color="Salmon"> .Map </store>
                  <network color="Salmon"> .Map </network>

                  <lock> #none </lock>

                  <active> .List:List </active>

                  <nextLoc> 0 </nextLoc>
                  <nextPid> 0 </nextPid>
                  <nextBCid> 0 </nextBCid>
                  <nextHCid> 0 </nextHCid>
                </T>
endmodule


module RUN // TODO: consider merging this module into INIT
  imports CONFIG

  syntax Map ::= gEnv(Map, Set) [function] // remove local variables from ENV
  rule gEnv((lval(X:Id, _) |-> _) M, SetItem(X) S) => gEnv(M, SetItem(X) S)
  rule gEnv(M, _) => M [owise]

/***
  run is called by value
  * #run(p, _:Expr) : yet to be reduced
  * #run(p, _:List) : list of values
***/
  syntax KItem ::= #run(Id, K) | "#wait" | "#done" | #init(Decls, List)

  rule [run]:
       <procs>...
         <proc>...
           <k> #run(X, VL:List) => #wait ...</k>
           <local> XS </local>
           <env> ENV </env>
      ...</proc>
         (.Bag =>
         <proc>
           <pid> I </pid>
           <name> X </name>
           <k> #init(DL,VL) ~> #done ~> SL </k>
           <local> .Set </local>
           <env> gEnv(ENV, XS) </env>
         </proc>)
    ...</procs>

       <proctype>...
         <procName> X </procName>
         <procParams> DL </procParams>
         <procBody> SL </procBody>
    ...</proctype>

       <nextPid> I => I +Int 1 </nextPid>

  rule [done]: <k> #wait => .K ...</k> <k> #done => .K ...</k>

  rule [init1]: #init(.Decls, _) => .K
  rule [init2]: #init((PT:PType X:Id ; _:Decls), .List) => PT X
  rule [init3]: #init((PT:PType X:Id ; _:Decls), (ListItem(V:Value) _:List)) => PT X = V
endmodule


module INIT
  imports RUN
//  imports CONFIG

  rule S:Spec S':Spec => S ~> S'

  rule [proctype]:
       <k> proctype X ( DL ) { SL } => .K ...</k>
       (.Bag => <proctype>
                  <procName> X </procName>
                  <procParams> DL </procParams>
                  <procBody> SL </procBody>
                  <gotoMap> .Map </gotoMap> // TODO: construct gotomap in the init phase
                </proctype>)
  [priority(0)]

  rule <k> active proctype X ( DL ) { SL } => (proctype X ( DL ) { SL } ~> #run(X, .List)) ...</k>
  [priority(0)]

  // auxiliary func for initializing store
  syntax Map ::= Int "..." Int "|->" K [function]
  rule N...M |-> _ => .Map  requires N >Int M
  rule N...M |-> K => N |-> K (N +Int 1)...M |-> K  requires N <=Int M

  // auxiliary func for initializing loc
  syntax Map ::= "lval" Id "::" Int "..." Int "|->" "loc" Int "..." Int [function]
  rule lval _ :: N...M |-> loc I...J => .Map  requires N >Int M orBool I >Int J
  rule lval X :: N...M |-> loc I...J => (lval(X,N) |-> loc(I)) (lval X :: (N +Int 1)...M |-> loc (I +Int 1)...J)  requires N <=Int M andBool I <=Int J

  // TODO: auxiliary func for initializing bch
  // TODO: auxiliary func for initializing hch

  // decl desugaring rules
  rule int X[I] => int X[I] = 0          rule int X => int X[1] = 0
  rule bool X[I] => bool X[I] = false    rule bool X => bool X[1] = false
  rule T:Type X = V:Value => T X[1] = V

  // heating & cooling for strict declarations
  // TODO: rule T:Type X = E:Expr => #eval(E) ~> T X[1] = HOLE requires _:Value :=/K E
  // TODO: rule #eval(V:Value) ~> T X[1] = (_ => V)

  rule [decl-prim]:
    <pid> PID </pid>
    <k> (_:PType X:Id[I:Int] = V:Value) => .K ...</k>
    <env> _:Map (.Map => lval X :: 0 ...(I -Int 1) |-> loc J...(J +Int I -Int 1)) </env> 
    <local> _:Set (.Set => #if PID ==K -1 #then .Set #else SetItem(X) #fi) </local>
    <store> _:Map (.Map => J...(J +Int I -Int 1) |-> V) </store>
    <nextLoc> J => J +Int I </nextLoc>
    requires I >Int 0

  // TODO: rule [decl-uch]
  // TODO: rule [decl-bch]
  // TODO: rule [decl-hch]
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
  rule eval(_ [ _:Int ] ? [ _ ], _, _, _) => false [owise]


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

  // Release (Controlled) - old
  /* rule <k> #rel => .K ...</k> <pid> PID </pid>
       <lock> PID => #none </lock> */ // acquire

  rule [rel]: <k> #rel => .K ...</k> <lock> _ => #none </lock>

  // Loose (Uncontrolled)
  rule [loose]: <lock> _:Int => #none </lock> [owise]
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
    ...</proctype> [priority(0)]

  // break - these rule only make sense if atomicity ctx is not altered
  rule (break ~> do _ od) => .K [priority(0)]
  rule break ~> (KI:KItem => .K) requires do _ od :/=K KI [priority(0)]
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
  rule <k> #sendMsg(ch(I), MSG) => .K ...</k>
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


module FIRE // BASICSTMT
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
  rule effect(X = E, PID) => #assign(X, 0, purify(E, PID)) // desugar
  rule effect(X [ E ] = E', PID) => effect(E', PID) ~> #assign(X, E, purify(E', PID))
  rule effect(X ! EL, _) => #send(X [ 0 ], EL) // desugar
  rule effect(X [ E ] ! EL, _) => #send(X [ E ], EL)
  rule effect(X ? EL, _) => #recv(X [ 0 ], EL) // desugar
  rule effect(X [ E ] ? EL, _) => #recv(X [ E ], EL)
endmodule


module SEQ // sequential decomposition
  imports PROMELA-SYNTAX

  syntax K ::= split(Seq) [function]
  rule split(S:Stmt ; SL:Seq) => S ~> split(SL)
  rule split(.Seq) => .K
endmodule


module LOAD // CONTROL-DECOMPOSITION or CONTROL-EFFECT as opposed GUARD-EFFECT
/*
  control effects are applied functionally, with "des"
*/
  imports SEQ
  imports BASIC
  imports ATOMICITY

  syntax KItem ::= "@[" K "]" // stores branch as a local computation K

  /* Control-Effect Decomposition */
  // assume 2nd arg is of form Stmt ~> K
  syntax Set ::= load(Bool, K) [function] // des(true, ...) means #rel is inserted appropriately
  rule load(true, BS:BasicStmt ~> K) => SetItem(@[ BS ~> K ])
  rule load(false, BS:BasicStmt ~> K) => load(true, BS ~> #rel ~> K)
  rule load(B, SL:Seq ~> K) => load(B, split(SL) ~> K)
  //rule load(B, (S ; S'):Seq ~> K) => load(B, S ~> S' ~> K) // FIXME
  //rule des(B, .Seq ~> K) => des(B, K) // FIXME
  rule load(true, atomic { SL } ~> K) => load(true, SL ~> K) // inner atomic
  rule load(false, atomic { SL } ~> K) => load(true, SL ~> #rel ~> K) // outermost atomic
  rule load(B, if (:: SL) OL fi ~> K) => load(B, SL ~> K) load(B, if OL fi ~> K)
  rule load(_, if .Optns fi ~> _) => .Set
  rule load(B, S:GotoStmt ~> K) => load(B, true ~> S ~> K)
  rule load(B, do OL od ~> K) => load(B, if OL fi ~> do OL od ~> K)

  // no assumption on the 2nd arg
/*
  syntax K ::= desK(Bool, K) [function] // extension of des
  rule desK(B, S ; SEQ:Seq ~> K) => des(B, S ~> SEQ ~> K) requires _:Goto :/=K S
  rule desK(_, S:Goto ; SEQ ~> K) => S ~> SEQ ~> K
  rule desK(B, .Seq ~> K) => desK(B, K)
  rule desK(_, #rel ~> K) => (#rel ~> desK(false, K))
  rule desK(_, .K) => .K
  rule desK(B, K) => des(B, K) [owise]
*/
endmodule


module PROMELA
  imports CONFIG
  imports INIT
  imports EXPRESSION
  imports LOAD
  imports FIRE
  imports GOTO

  syntax Stmt ::= "stop"
  //rule #freeze => .K // this has priority issue: it always happens first that the load rule etc.

  syntax K ::= spload(Bool, K) [function]
  rule spload(B, SL:Seq) => spload(B, split(SL))
  rule spload(B, S:Stmt ~> K) => load(B, S) ~> K requires (_:DeclStmt :/=K S)
  rule spload(_, K) => K [owise]

// original spload: uncomment this block to rollback
/*
  rule [spload]:
       <pid> PID </pid> <lock> LCK </lock>
       <k> SL:Seq => spload(PID ==K LCK, SL) ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
    [priority(151)]


  rule [split]:
       <pid> PID </pid> <lock> LCK </lock>
       <k> SL:Seq => split(SL) ...</k>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
    [priority(152)]


  rule [load]:
    <pid> PID </pid> <lock> LCK </lock>
    <k> S:Stmt => load(PID ==K LCK, S) ...</k>
    requires (_:GotoStmt :/=K S) andBool (_:DeclStmt :/=K S)
             //andBool (LCK ==K #none orBool LCK ==K PID) // this cond should not be here
  [priority(153)]
*/

  rule [fire]:
    <pid> PID </pid> <lock> LCK => PID </lock>
    <k> ((SetItem(@[BS ~> K]) _:Set) ~> K')
        => (effect(BS, PID') ~> K ~> K')
    </k>
    <env> ENV </env> <store> STR </store> <network> NET </network>
    <nextPid> PID' </nextPid>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool isExec(BS, ENV, STR, NET, PID') ==K true
  //[priority(51)]



  rule [hs-fire] :
    <proc>...
      <pid> PID1 </pid>
      <k>
        (SetItem(@[ X1 [ E1 ] ! EL1 ~> K1 ]) _) => SetItem(@[ true ~> K1 ]) // to prevent early release due to double #rel by reload
   ...</k>
      <env> ENV1 </env>
 ...</proc>
    <proc>...
      <pid> PID2 </pid>
      <k>
        (SetItem(@[ X2 [ E2 ] ? EL2 ~> K2 ]) _) =>
        (#if LCK ==K PID1 #then #toss(PID1) #else .K #fi ~> #recvMsg(EL2, m(evalList(EL1, ENV1, STR, NET))) ~> K2)
   ...</k>
      <env> ENV2 </env>
 ...</proc>
    <lock> LCK => PID2 </lock>
    <store> STR </store>
    <network> NET </network>
    requires (LCK ==K #none orBool LCK ==K PID1 orBool LCK ==K PID2) // check lock
             andBool eval(X1 [ E1 ], ENV1, STR, NET) ==HChan eval(X2 [ E2 ], ENV2, STR, NET) // check HChan eq
             // andBool match(EL,AL)

  syntax Bool ::= Value "==HChan" Value [function]
  rule hs(I) ==HChan hs(I) => true
  rule _ ==HChan _ => false [owise] 

  syntax KItem ::= #toss(Int)
  rule [toss1]: <k> (.K => KI) ~> #toss(_) ~> (KI:KItem => .K) ...</k> requires KI =/=K #rel
  rule [toss2]: <k> (#toss(I) ~> #rel) => .K ...</k> <lock> _ => I </lock>




  // EXPERIMENTAL
  // TODO: global control for spload
  syntax KItem ::= #normalize(List) // TODO: maybe fix name to #spload
  syntax Bool ::= sploadable(KItem) [function]
  rule sploadable(S) => ((_:Stmt :=K S) orBool (_:Seq :=K S)) andBool (_:DeclStmt :/=K S)

/*
  rule [end]:
    <active> PL => </active>
    <pid> PID </pid>
    <k> .K </k>
  requires PID in PL
*/


/* for freeze
  rule [fire]:
    <pid> PID </pid> <lock> LCK => PID </lock>
    <k> ((SetItem(@[BS ~> K]) _:Set) ~> K')
        => (effect(BS, PID') ~> K ~> K')
    </k>
    <env> ENV </env> <store> STR </store> <network> NET </network>
    <nextPid> PID' </nextPid>
    requires (LCK ==K #none orBool LCK ==K PID) // check lock
             andBool isExec(BS, ENV, STR, NET, PID') ==K true
*/


  // same priority with fire -- regarded as a pseudo basic statement
  // freeze by preventing other processes from loading
  syntax KItem ::= "#freeze"
  rule [freeze]:
    <active> _PL => .List </active>
    <lock> #none => #frozen </lock> 
    <k> #freeze => .K </k>

  rule [spload-freeze]:
       <lock> #none </lock>
       <proc>...
         <pid> PID </pid>
         <k> #freeze ...</k>
    ...</proc>
       <proc>...
         <pid> -1 </pid>
         <k> #normalize((ListItem(PID) => .List) _) </k>
    ...</proc>
    [priority(2)]



  rule [synch-init1]:
    <lock> #none </lock>
    <active> PL </active> // list of active procs in increasing order
    <pid> -1 </pid> // global controller
    <k> .K => #normalize(PL) </k> 
  [priority(1)] // IMPORTANT: this should happen before anything else!

  rule [synch-init2]:
    <lock> PID => #none </lock>
    <active> PL </active> // list of active procs in increasing order
    <proc>...
      <pid> PID </pid>
      <k> #rel => .K ...</k>
 ...</proc>
    <proc>...
      <pid> -1 </pid>
      <k> #normalize(.List => PL) </k>
 ...</proc>
  [priority(1)] // IMPORTANT: this should happen before anything else!
 

  rule [spload-true]:
       <lock> #none </lock>
       <proc>...
         <pid> PID </pid>
         <k> KI:KItem => spload(false, KI) ...</k>
    ...</proc>
       <proc>...
         <pid> -1 </pid>
         <k> #normalize((ListItem(PID) => .List) _) </k>
    ...</proc>
    requires sploadable(KI)
    [priority(2)]

  rule [spload-false]:
       <lock> #none </lock>
       <proc>...
         <pid> PID </pid>
         <k> KI:KItem ...</k>
    ...</proc>
       <proc>...
         <pid> -1 </pid>
         <k> #normalize((ListItem(PID) => .List) _) </k>
    ...</proc>
    requires notBool sploadable(KI)
    [priority(2)]

  rule [spload-end]: // FIXME: this is ad-hoc
       <lock> #none </lock>
       <proc>...
         <pid> PID </pid>
         <k> .K </k>
    ...</proc>
       <proc>...
         <pid> -1 </pid>
         <k> #normalize((ListItem(PID) => .List) _) </k>
    ...</proc>
    [priority(2)]


  rule [spload-atomic]: // spload while in atomic block
       <lock> PID:Int </lock>
       <proc>...
         <pid> PID </pid>
         <k> KI:KItem => spload(true, KI) ...</k>
    ...</proc>
    requires sploadable(KI)
    [priority(2)]


endmodule
