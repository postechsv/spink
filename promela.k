module PROMELA
  imports DOMAINS-SYNTAX

  //syntax Spec ::= List{Mdle, " "}

  syntax Spec ::= Proc
                | Decl
                | Spec Spec [symbol(Specs), left]

  syntax Proc ::=  Active "proctype" Id "(" Decls ")" "{" Stmt "}"
                 | "proctype" Id "(" Decls ")" "{" Stmt "}"

  syntax Active ::= "active" | "active" "[" Const "]"

  syntax Decl ::= Type Ivar [symbol(Decl)]

  syntax Decls ::= List{Decl, ";"}

  syntax Type ::= "int" [symbol(Int)] | "bool" [symbol(Bool)] | "chan" [symbol(Chan)]

  syntax Types ::= List{Type, ","}

  syntax Stmt ::= "skip" [symbol(skip)] | Stmt ";" | Stmt ";" Stmt [left, prefer] | Decl | Const | Expr
                | Vref "=" Expr [symbol(=)] | "run" Id "(" Exprs ")"  | "atomic" "{" Stmt "}" | "if" Optns "fi"
                | Vref "!" Exprs | Vref "?" Exprs

  syntax Expr ::= Const | Vref | Expr "+" Expr 
                | Expr "*" Expr 
                | Expr "==" Expr
                | Expr "||" Expr

  syntax Exprs ::= List{Expr, ","} [symbol(Exprs)]

  syntax Optn ::= "::" Stmt

  syntax Optns ::= List{Optn, " "}

  syntax Ivar ::= Ivar "," Ivar | Vref | Vref "=" Expr | Vref "=" "[" Const "]" "of" "{" Types "}"

  syntax Vref ::= Id [symbol(Var)] | Id "[" Expr "]"

  syntax Const ::= Value

  syntax Value ::= Int | Bool

  syntax Id ::= "#defaultID" [token]

endmodule


