(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

Require Import Coqlib.
Require Import Integers.
Require Import Floats.
Require Import AST.
Require Import Lop.
Require Import Lustre.

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
  | Tshort : typeL                          (**r integer types, signed 16 bits *)
  | Tushort : typeL                         (**r integer types, unsigned 16 bits  *)
  | Tint : typeL                            (**r integer types, signed 32 bits *)
  | Tuint : typeL                           (**r integer types, unsigned 32 bits *)
  | Tfloat : typeL                          (**r floating-point types, 32 bits *)
  | Treal : typeL                           (**r floating-point types, 64 bits *)
  | Tbool : typeL                           (**r bool types *)
  | Tchar : typeL                           (**r char types *)
  | Tarray : ident -> typeL -> Z -> typeL   (**r array types: array_type_id(ty^len) *)
  | Tstruct : ident -> fieldlistL -> typeL  (**r struct types: struct_type_id {label1_id: type1; ...} *)
  | Tenum : list ident -> typeL    (**r enum types: enum_type_id {value1_id, ...} *)         

with fieldlistL : Type :=
  | Fnil : fieldlistL
  | Fcons : ident -> typeL -> fieldlistL -> fieldlistL.

Lemma type_eqL: forall (ty1 ty2: typeL), {ty1=ty2} + {ty1<>ty2}
with fieldlist_eqL: forall (fld1 fld2: fieldlistL), {fld1=fld2} + {fld1<>fld2}.
Proof.
  repeat (decide equality).
  generalize ident_eq zeq. intros E1 E2. 
  decide equality.
Defined.

Opaque type_eqL fieldlist_eqL.

(** const_block 
     Const block consisting of all character constants *)

Inductive constL : Type := 
  | ShortConstL: int -> constL
  | UshortConstL: int -> constL
  | IntConstL: int -> constL
  | UintConstL: int -> constL
  | CharConstL: int -> constL
  | FloatConstL: float32 -> constL
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
  | Nodehandler : ident -> bool -> list typeL -> suboperator
  | PrefixL_unary : unary_operationL -> suboperator
  | PrefixL_binary : binary_operationL -> suboperator. 

Inductive exprT : Type := 
  | EconstT : const -> typeL -> exprT
  | EvarT : ident -> typeL -> clock -> exprT
  | ListExprT : expr_listT -> exprT                                           (**r list expression *)
  | ApplyExprT : operatorT -> expr_listT ->  exprT 	              (**r operator application *)
  | EconstructT : struct_listT -> exprT                                      (**r construct a struct, e.g {label1 : 3, label2 : false} *)
  | EarrayaccT : exprT -> int -> exprT                                     (**r expr[i], access to (i+1)th member of an array "expr" *)
  | EarraydefT :  exprT -> int -> exprT                               (**r expr ^ i, an array of size "i" with every element "expr" *)
  | EarraydiffT : expr_listT ->  exprT                                      (**r [list expression], build an array with elements "list expression", e.g [1,2]*)
  | EarrayprojT: exprT -> expr_listT -> exprT ->  exprT                     (**r dynamic projection, e.g (2^3^4.[7] default 100^3), value is 100^3 *) 
  | EarraysliceT : exprT -> int -> int -> exprT                            (**r a [i..j] is the sliced array [a_i, a_i+1, ... , a_j]*) 
  | EmixT : exprT -> label_index_listT -> exprT -> exprT                   (**r construct a new array or struct, e.g {label1:2^3} with label1.[0] = 7, value is {label1:[7,2]} *)
  | EunopT : unary_operationL -> exprT -> exprT                            (**r unary operation *)
  | EbinopT : binary_operationL -> exprT -> exprT -> exprT                 (**r binary operation *)
  | EfieldT : exprT -> ident -> exprT                                      (**r access to a member of a struct *)
  | EpreT : exprT -> exprT                              (**r pre : shift flows on the last instant backward, producing an undefined value at first instant*)
  | EfbyT : expr_listT -> int -> expr_listT -> exprT  (**r fby : fby(b; n; a) = a -> pre fby(b; n-1; a) *) 
  | EarrowT : exprT -> exprT -> exprT                                         (**r -> : fix the inital value of flows*)
  | EwhenT : exprT -> clock -> exprT                                          (**r x when h: if h=false, then no value; otherwise x *)
  | EcurrentT: exprT ->  exprT   
  | EmergeT: ident -> pattern_listT -> exprT   
  | EifT : exprT -> exprT -> exprT -> exprT                                   (**r conditional*)
  | EcaseT : exprT -> pattern_listT -> exprT                                  (**r case *)
  | EboolredT: int -> int -> exprT -> exprT
  | EdieseT: exprT -> exprT  (**r #(a1, ..., an) -> boolred(0,1,n)[a1, ..., an] *)
  | EnorT: exprT ->  exprT  (**r nor(a1, ..., an) boolred(0,0,n)[a1, ..., an] *)

with expr_listT : Type :=
  | Enil: expr_listT
  | Econs: exprT -> expr_listT -> expr_listT

with struct_listT: Type :=
  | EstructNil: struct_listT
  | EstructCons: ident -> exprT -> struct_listT -> struct_listT

with label_index_listT: Type :=
  | Lnil: label_index_listT
  | LconsLabelT: ident -> label_index_listT -> label_index_listT
  | LconsIndexT: exprT -> label_index_listT -> label_index_listT

with pattern_listT : Type :=
  | PatternNilT : pattern_listT
  | PatternConT : patn -> exprT -> pattern_listT -> pattern_listT

with operatorT : Type :=  
  | SuboperatorT : suboperator -> operatorT
  | IteratorT : iterator_operation -> suboperator -> int -> operatorT.

(** * Equation *)

Inductive equationT : Type :=
  | EquationT: vars -> exprT -> equationT.

(** * Node *)

(** Node : kind -> ID -> parameters -> returns -> locals -> body *)

Record nodeT : Type :=
  | NodeT : bool -> ident -> vars -> vars -> vars -> list equationT -> nodeT.    

(** * Program *)

Inductive programT : Type := mkprogramT{
  type_blockT : list (ident*typeL);
  const_blockT : list (ident*typeL*constL);
  node_blockT : list nodeT;
  node_mainT : ident
}.

