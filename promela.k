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

  syntax Stmt ::= "skip" | Stmt ";" | Stmt ";" Stmt [left, prefer] | Decl | Const | Expr
                | Vref "=" Expr | "run" Id "(" Exprs ")"  | "atomic" "{" Stmt "}" | "if" Optns "fi"
                | Vref "!" Exprs | Vref "?" Exprs

  syntax Expr ::= Const | Vref
                | "-" Expr | "!" Expr
                | Expr "+" Expr | Expr "-" Expr | Expr "*" Expr | Expr "/" Expr 
                | Expr "&&" Expr | Expr "||" Expr | Expr "==" Expr | Expr "!=" Expr 

  syntax Exprs ::= List{Expr, ","}

  syntax Optn ::= "::" Stmt

  syntax Optns ::= List{Optn, " "}

  syntax Ivar ::= Ivar "," Ivar | Vref | Vref "=" Expr | Vref "=" "[" Const "]" "of" "{" Types "}"

  syntax Vref ::= Id | Id "[" Expr "]"

  syntax Const ::= Value

  syntax Value ::= Int | Bool

  syntax Id ::= "#Configurator" [token]

endmodule

module PROMELA-CONFIG
  imports PROMELA-SYNTAX

  syntax Lock ::= Int | "#unlocked"
  syntax KItem ::= "#acq" | "#rel"

  configuration <T color="yellow">
                  <proctypes>
                    <proctype multiplicity="*" type="Map" initial="">
                      <procName> #Configurator </procName>
                      <procParams> .Decls </procParams>
                      <procBody> skip </procBody>
                      <gotoMap> .Map </gotoMap>
                    </proctype>
                  </proctypes>

                  <procs> // active procs
                    <proc multiplicity="*" type="Map" color="orange" initial="">
                      <pid> -1 </pid>
                      <k color="green"> $PGM:Spec </k>
                      <env color="LightSalmon"> .Map </env>
                    </proc>
                  </procs> 

                  <store color="Salmon"> .Map </store>
                  <nextLoc> 0 </nextLoc> <nextPid> 0 </nextPid>

                </T>

endmodule

module PROMELA
  imports PROMELA-CONFIG
  imports DOMAINS

  /****************
  BASIC DEFINITIONS
  *****************/

  syntax Effect ::= "sil" | "lck"

  syntax KItem ::= "null" | loc(Int) | lval(Id, Int)
                 | choice(Effect, K) // Effecful Choice
                 //| #runNProcs(Id, Exprs, Int)

  syntax K ::= dupKItems(KItem, Int) [function]
  rule dupKItems(KI, 1) => KI
  rule dupKItems(KI, N) => KI ~> dupKItems(KI, N -Int 1) [owise]









  // Spec
  rule S1:Spec S2:Spec => S1 ~> S2 

  // Decl
  rule T:Type I1:Ivar , I2:Ivar => T I1 ~> T I2


  // Decl for value types
  rule T:Type X:Id => T (X [ 1 ]) // sugar
  rule _:Type _:Id [ 0 ] => .K
  rule <k> T:Type X:Id [ I:Int ] => T X [ I -Int 1 ] ...</k>
       <env> Env => Env[lval(X, I -Int 1) <- loc(L)] </env> 
       <store>... .Map => L |-> 0 ...</store>
       <nextLoc> L => L +Int 1 </nextLoc> [owise] // L may not be consecutive: int x[2] || int y[2]

  // Decl for Proc
  rule active proctype X:Id ( DL:Decls ) { S:Stmt }
    => active [ 1 ] proctype X:Id ( DL:Decls ) { S:Stmt } // sugar
  //rule active [ 0 ] proctype _ ( _ ) { _ } => .K
  rule active [ I:Int ] proctype X:Id ( DL:Decls ) { S:Stmt } 
    => proctype X:Id ( DL:Decls ) { S:Stmt } ~> dupKItems(run X ( .Exprs ), I)

  // Proctype
  rule <k> proctype X:Id ( DL:Decls ) { S:Stmt } => .K ...</k>
       (.Bag => <proctype>...
                  <procName> X </procName>
                  <procParams> DL </procParams>
                  <procBody> S </procBody>
                ...</proctype>)


  // Sequence
  rule <k> SetItem(choice(_E, ((S1 ; S2):Stmt => S1 ~> S2) ~> K)) _:Set ...</k>


  /*******************************************************
        BASIC ACTIONS
  *******************************************************/
  //rule <k> (SetItem(choice(_E, _K)) => .Set) ...</k>


  // Assign
  rule <k> SetItem(choice(_E, ((X [ I:Int ] = V:Value):Stmt => .K) ~> K)) (_:Set => .Set) ...</k>
       <env>... lval(X, I) |-> loc(L) ...</env>
       <store>... L |-> (_ => V) ...</store>
       //<pid> J </pid> <exc> J </exc>


  // Run
  rule <k> run X:Id ( _EL:Exprs ) => .K ...</k> <env> ENV </env>
       <proctype>... <procName> X </procName> <procParams> _DL </procParams> <procBody> S </procBody> ...</proctype>
       <nextPid> L => L +Int 1 </nextPid>
       (.Bag => <proc>...
                  <pid> L </pid>
                  //<pName> X </pName>
                  <k> SetItem(choice(sil, S)) SetItem(choice(sil, 42)) SetItem(choice(sil, 43)) </k> // TODO DL = EL ~> S
                  <env> ENV </env> // inherits ENV from the parent
             ...</proc>)

endmodule
