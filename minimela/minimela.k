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
                     //| Vref "=" Expr // Assign
                     | Id "=" Expr [macro] // Assign-alt
                     | Id "[" Expr "]" "=" Expr // Assign-alt
                     | "skip"

  syntax Stmt ::= BasicStmt | Stmt ";" | Stmt ";" Stmt [left, prefer]
                | "atomic" "{" Stmt "}"
                | "if" Optns "fi" | "do" Optns "od"
                | "break" 

//  syntax Stmt ::= "skip" | Stmt ";" | Stmt ";" Stmt [left, prefer] | Decl | Const | Expr
//                | Vref "=" Expr | "run" Id "(" Exprs ")"  | "atomic" "{" Stmt "}" | "if" Optns "fi"
//                | Vref "!" Exprs | Vref "?" Exprs

  syntax Expr ::= Const | Vref
                | "-" Expr | "!" Expr
                | Expr "+" Expr | Expr "-" Expr | Expr "*" Expr | Expr "/" Expr 
                | Expr "<" Expr | Expr "<=" Expr | Expr ">" Expr | Expr ">=" Expr 
                | Expr "&&" Expr | Expr "||" Expr | Expr "==" Expr | Expr "!=" Expr 

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
                  <lock> #none </lock>
                  <nextLoc> 0 </nextLoc>
                 // <nextPid> 0 </nextPid>

                </T>

endmodule

module MINIMELA
  imports MINIMELA-CONFIG
  imports DOMAINS

  /****************
  BASIC DEFINITIONS
  *****************/


  syntax KItem ::= "null" | loc(Int) | lval(Id, Int)
                 | choice(SEffect, K) // Effecful Choice

  syntax K ::= dupKItems(KItem, Int) [function]
  rule dupKItems(KI, 1) => KI
  rule dupKItems(KI, N) => KI ~> dupKItems(KI, N -Int 1) [owise]

  syntax Value ::= eval(Expr, Map, Map) [function]
  rule eval(V:Value, _, _) => V
  rule eval(X, ENV, STR) => eval(X[0], ENV, STR) // desugar
  rule eval(X[I], (lval(X, I) |-> loc(L)) _ENV, (L |-> V) _STR) => V
  rule eval(E1 == E2, ENV, STR) => eval(E1, ENV, STR) ==K eval(E2, ENV, STR)
  rule eval(E1 + E2, ENV, STR) => {eval(E1, ENV, STR)}:>Int +Int {eval(E2, ENV, STR)}:>Int
  rule eval(E1 < E2, ENV, STR) => {eval(E1, ENV, STR)}:>Int <Int {eval(E2, ENV, STR)}:>Int
  rule eval(E1 <= E2, ENV, STR) => {eval(E1, ENV, STR)}:>Int <=Int {eval(E2, ENV, STR)}:>Int
  rule eval(E1 > E2, ENV, STR) => {eval(E1, ENV, STR)}:>Int >Int {eval(E2, ENV, STR)}:>Int
  rule eval(E1 >= E2, ENV, STR) => {eval(E1, ENV, STR)}:>Int >=Int {eval(E2, ENV, STR)}:>Int











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

  // Atomic TODO: check nested (inner atomic should not generate #rel)
  rule <k> 
         SetItem(choice(_ => acq, 
           (atomic { S } => (S ~> #rel))
           ~> _K))
         _:Set
    ...</k>

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
       <env> ENV </env>  <store> STR </store>
    requires eval(EXP, ENV, STR) ==K true

  // Assign - TODO: eval(I)
  rule (X:Id = V):Stmt => (X [ 0 ] = V):Stmt // desugar
  rule <pid> PID </pid>
       <k>
         SetItem(choice(EFF => sil, // init side-effect
           ((X [ I:Int ] = EXP):Stmt => .K) ~> _K))
         (_:Set => .Set) // side-effect : choose
    ...</k>
       <env> (lval(X, I) |-> loc(L)) ENV </env>
       <store> STR => STR[L <- eval(EXP, (lval(X, I) |-> loc(L)) ENV, STR)] </store>
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
       <store> STR (.Map => L ... (L +Int I -Int 1) |-> eval(EXP, ENV, STR)) </store>
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
