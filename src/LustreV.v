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
Require Import Ctypes.
Require Import Cltypes.
Require Import Lident.

(** * Common syntax *)

(** Output parameters, Input parameters, and local variables*)

Definition vars := list (ident * type * clock).

(** * Expressions *)

Inductive operator: Type:=
  | Oiteratorcall : iterator_operation -> calldef ->  operator
  | Omapary: binary_operationL -> operator
  | Omaptycmp: bool -> operator
  | Omapunary: unary_operationL -> operator
  | Ofoldary: binary_operationL -> operator
  | Ofoldunary: unary_operationL -> operator
  | Oarydef: operator
  | Oaryslc: int -> operator.

(** All expressions are annotated with their types and clocks. *)

Inductive expr : Type := 
  | Econst : const -> type -> clock -> expr
  | Evar : ident -> type -> clock -> expr
  | ListExpr : expr_list -> expr                                           (**r list expression *)
  | Ecall: calldef -> expr_list -> list (type * clock) -> expr
  | Efor : bool -> operator -> int -> expr_list -> list (type * clock) -> expr 	              (**r operator application *)
  | Econstruct : expr_list -> (type * clock) -> expr                                      (**r construct a struct, e.g {label1 : 3, label2 : false} *)
  | Earrayacc : expr -> int -> (type * clock) -> expr                                     (**r expr[i], access to (i+1)th member of an array "expr" *)
  | Earraydiff : expr_list -> (type * clock) -> expr                                      (**r [list expression], build an array with elements "list expression", e.g [1,2]*)
  | Earrayproj: expr -> expr_list -> expr -> (type * clock) -> expr                     (**r dynamic projection, e.g (2^3^4.[7] default 100^3), value is 100^3 *) 
  | Emix : expr -> label_index_list -> expr -> (type * clock) -> expr                   (**r construct a new array or struct, e.g {label1:2^3} with label1.[0] = 7, value is {label1:[7,2]} *)
  | Eunop : unary_operationL -> expr -> (type * clock) -> expr                            (**r unary operation *)
  | Ebinop : binary_operationL -> expr -> expr -> (type * clock) -> expr                 (**r binary operation *)
  | Efield : expr -> ident -> (type * clock) -> expr                                      (**r access to a member of a struct *)
  | Epre : list ident -> expr -> list (type * clock) -> expr                              (**r pre : shift flows on the last instant backward, producing an undefined value at first instant*)
  | Efby : list (ident) -> expr_list -> expr_list -> list (type * clock) -> expr  
  | Efbyn : list (ident*ident*ident) -> expr_list -> int -> expr_list -> list (type * clock) -> expr  (**r fby : fby(b; n; a) = a -> pre fby(b; n-1; a) *) 
  | Earrow : expr -> expr -> list (type * clock) -> expr                                         (**r -> : fix the inital value of flows*)
  | Ewhen : expr -> clock -> list (type * clock) -> expr                                          (**r x when h: if h=false, then no value; otherwise x *)
  | Ecurrent: list ident -> expr ->  list (type * clock) -> expr   
  | Emerge: ident -> type -> pattern_list -> list (type * clock) -> expr   
  | Eif : expr -> expr -> expr -> list (type * clock) -> expr                                   (**r conditional*)
  | Ecase : expr -> pattern_list -> list (type * clock) -> expr                                  (**r case *)
  | Eboolred: int -> int -> expr -> (type * clock) -> expr
  | Ediese: expr -> (type * clock) -> expr  (**r #(a1, ..., an) -> boolred(0,1,n)[a1, ..., an] *)
  | Enor: expr -> (type * clock) -> expr  (**r nor(a1, ..., an) boolred(0,0,n)[a1, ..., an] *)
  | Etypecmp : bool -> expr -> expr -> (type * clock) -> expr
  | Eprefix: binary_operationL -> expr_list -> (type * clock) -> expr

with expr_list : Type :=
  | Enil: expr_list
  | Econs: expr -> expr_list -> expr_list

with label_index_list: Type :=
  | Lnil: label_index_list
  | LconsLabel: ident -> label_index_list -> label_index_list
  | LconsIndex: expr -> label_index_list -> label_index_list

with pattern_list : Type :=
  | PatternNil : pattern_list
  | PatternCon : patn -> expr -> pattern_list -> pattern_list.

Fixpoint typeclock_of (e: expr) : list (type * clock) := 
  match e with
  | Econst _ t c => (t,c)::nil
  | Evar _ t c => (t,c)::nil                                                   
  | ListExpr l => typeclocks_of l   
  | Ecall _ _ tcl => tcl                                      
  | Efor _ _ _ _ tcl => tcl  
  | Econstruct _ tc => tc::nil  
  | Earrayacc _ _ tc => tc::nil  
  | Earraydiff _ tc => tc::nil  
  | Earrayproj _ _ _ tc => tc::nil  
  | Emix _ _ _ tc => tc::nil  
  | Eunop _ _ tc => tc::nil  
  | Ebinop _ _ _ tc => tc::nil  
  | Efield _  _ tc => tc::nil  
  | Epre _ _ tcl => tcl  
  | Efby _ _ _ tcl => tcl  
  | Efbyn _ _ _ _ tcl => tcl  
  | Earrow _ _ tcl => tcl  
  | Ewhen _ _ tcl => tcl
  | Ecurrent _ _ tcl => tcl
  | Emerge _ _ _ tcl => tcl
  | Eif _ _ _ tcl => tcl  
  | Ecase _ _ tcl => tcl  
  | Eboolred _ _ _ tc => tc:: nil 
  | Ediese _ tc => tc:: nil 
  | Enor _ tc => tc :: nil
  | Etypecmp _ _ _ tc => tc :: nil
  | Eprefix _ _ tc => tc :: nil
  end

with typeclocks_of (e: expr_list) : list (type * clock) :=
  match e with 
  | Enil => nil
  | Econs e etl => app (typeclock_of e) (typeclocks_of etl)
  end.

(** * Equation *)

Inductive equation : Type :=
  | Equation: vars -> expr -> equation.

(** * Node *)

Record node: Type := mknode {
  nd_kind: bool;                 (**r node kind. *)
  nd_args: vars;                 (**r input parameters. *)
  nd_rets: vars;                 (**r output parameters. *)
  nd_vars: vars;                 (**r local variables. *)
  nd_eqs: list equation         (**r statement. *) 
}.

(** * Program *)

Definition program : Type := general_program node.

Scheme exprs_ind2 :=
  Induction for expr Sort Prop
with expr_lists_ind2 :=
  Induction for expr_list Sort Prop
with pattern_lists_ind2 :=
  Induction for pattern_list Sort Prop
with label_index_list_ind2 :=
  Induction for label_index_list Sort Prop.

Scheme exprs_ind3 := Minimality for expr Sort Prop
  with expr_lists_ind3 := Minimality for expr_list Sort Prop
  with pattern_lists_ind3 := Minimality for pattern_list Sort Prop
  with label_lindex_lists_ind3 := Minimality for label_index_list Sort Prop.  
