Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Lop.
Require Import Lustre.
Require Import Maps.

(** * Global Declares *)

(** * Types *)   

(** Types include short (signed 16 bits), ushort (unsigned 16 bits),int(signed 32 bits),
  uint(unsigned 32 bits), float (32 bits), real (64 bits), bool(true or false), char, 
  array, struct and enum. *) 
 
(** The syntax of type expressions.  Some points to note:
- struct type, e.g type s1 = { n : int, m : real } is expressed by syntax as below:
       Tstruct "s1" (Fcons "n" (Tint)
                    (Fcons "m" (Treal)
                    Fnil))
- no recursive type, e.g type s = { m : s } is not allowed, although it canbe expressed by syntax. 
*)
 
Inductive typeL : Type :=
  | Tint : typeL                            (**r integer types, signed 32 bits *)
  | Treal : typeL                           (**r floating-point types, 64 bits *)
  | Tbool : typeL                           (**r bool types *)
  | Tarray : ident -> typeL -> Z -> typeL   (**r array types: array_type_id(ty^len) *)
  | Tstruct : ident -> fieldlistL -> typeL  (**r struct types: struct_type_id {label1_id: type1; ...} *)
  | Tenum : list ident -> typeL    (**r enum types: enum_type_id {value1_id, ...} *)         

with fieldlistL : Type :=
  | Fnil : fieldlistL
  | Fcons : ident -> typeL -> fieldlistL -> fieldlistL.

(** const_block 
     Const block consisting of all character constants *)

Inductive constL : Type := 
  | IntConstL: int -> constL
  | RealConstL: float -> constL
  | BoolConstL: bool -> constL
  | ConstructConstL : const_listL -> constL     (**r E.g struct {label1 : 1, label2 : 2}, or array [1, 2] *) 
  | ID : ident -> constL               (**r to define other constant by character constant *)     

with const_listL : Type :=
  | ConstNilL : const_listL
  | ConstConL : constL -> const_listL -> const_listL.

(** * Expressions *)

Definition vars := list (ident * typeL * clock).

Inductive suboperator : Type := 
  | Nodehandler : ident -> bool -> list typeL -> suboperator.

Inductive exprT : Type := 
  | EconstT : const -> typeL -> exprT
  | EvarT : ident -> typeL -> clock -> exprT
  | ListExprT : expr_listT -> exprT                                           (**r list expression *)
  | ApplyExprT : suboperator -> expr_listT ->  exprT 	              (**r operator application *)
  | EconstructT : struct_listT -> exprT                                      (**r construct a struct, e.g {label1 : 3, label2 : false} *)
  | EarrayaccT : exprT -> int -> exprT                                     (**r expr[i], access to (i+1)th member of an array "expr" *)
  | EarraydefT :  exprT -> int -> exprT                               (**r expr ^ i, an array of size "i" with every element "expr" *)
  | EarraydiffT : expr_listT ->  exprT                                      (**r [list expression], build an array with elements "list expression", e.g [1,2]*)
  | EunopT : unary_operationL -> exprT -> exprT                            (**r unary operation *)
  | EbinopT : binary_operationL -> exprT -> exprT -> exprT                 (**r binary operation *)
  | EfieldT : exprT -> ident -> exprT                                      (**r access to a member of a struct *)
  | EpreT : exprT -> exprT                              (**r pre : shift flows on the last instant backward, producing an undefined value at first instant*)
  | EfbyT : expr_listT -> int -> expr_listT -> exprT  (**r fby : fby(b; n; a) = a -> pre fby(b; n-1; a) *) 
  | EarrowT : exprT -> exprT -> exprT                                         (**r -> : fix the inital value of flows*)
  | EwhenT : exprT -> clock -> exprT                                          (**r x when h: if h=false, then no value; otherwise x *)
  | EcurrentT: exprT ->  exprT   
  | EifT : exprT -> exprT -> exprT -> exprT                                   (**r conditional*)
  | EdieseT: exprT -> exprT  (**r #(a1, ..., an) -> boolred(0,1,n)[a1, ..., an] *)
  | EnorT: exprT ->  exprT  (**r nor(a1, ..., an) boolred(0,0,n)[a1, ..., an] *)

with expr_listT : Type :=
  | Enil: expr_listT
  | Econs: exprT -> expr_listT -> expr_listT

with struct_listT: Type :=
  | EstructNil: struct_listT
  | EstructCons: ident -> exprT -> struct_listT -> struct_listT.

Inductive megaT : Type :=
  | MegaT : ident -> ident -> megaT.

Inductive ctrl_exprT : Type :=
  | ExprT : exprT -> ctrl_exprT
  | MegaExprT : megaT -> ctrl_exprT.

Inductive ctrl_lhs : Type :=
  | IdentT : vars -> ctrl_lhs
  | MegaLhsT : megaT -> ctrl_lhs.

(** * Equation *)

Inductive equationT : Type :=
  | EquationT: vars -> exprT -> equationT.

Inductive ctrl_equationT : Type :=
  | CtrlEquationT: ctrl_lhs -> ctrl_exprT -> ctrl_equationT.

(** * Node *)

(** Node : kind -> ID -> parameters -> returns -> locals -> body *)

Inductive nodeT : Type :=
  | NodeT : bool -> ident -> vars -> vars -> vars -> list equationT -> nodeT.

Inductive widgetT : Type :=
  | WidgetT : ident -> vars -> vars -> widgetT.

Inductive ctrlT : Type :=
  | CtrlT : ident -> vars -> list ctrl_equationT -> ctrlT.

(** * Program *)
Definition widgetenv := PTree.t widgetT.
Definition empty_widgetenv := PTree.empty widgetT.

Record programT : Type := mkprogramT {
  type_blockT : list (ident*typeL);
  const_blockT : list (ident*typeL*constL);
  node_blockT : list nodeT;
  controlT : ctrlT;
  widget_blockT : widgetenv;
  node_mainT : ident
}.
