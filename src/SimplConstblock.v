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

(** calculate the value of const ident. *)

Require Import Coqlib.
Require Import Ctypes.
Require Import Cltypes.
Require Import AST.
Require Import Errors.
Require Import List.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Bool.
Require Import Globalenvs.
Require Import Lop.
Require Import Lustre.
Require Import LustreS.
Require Import Lident.
Require Import Ltypes.
Require Import Cop.


Local Open Scope error_monad_scope.

Definition trans_init_data (a: init_data)(sconsts : list (ident * globvar type))
  : res (list init_data) :=  
  match a with
  | Init_addrof id ofs =>
    do (_, gv) <- get_nt_byid id sconsts;
    OK (gvar_init gv)  
  | _ => OK (a :: nil)
  end.

Fixpoint trans_init_datas (l: list init_data)(sconsts : list (ident * globvar type))
  : res (list init_data) :=  
  match l with
  | nil => OK nil
  | a :: tl =>
    do first <- trans_init_data a sconsts;
    do rest <- trans_init_datas tl sconsts;
    OK (first ++ rest)
  end.  

Definition trans_gconst (const: ident * globvar type)(sconsts : list (ident * globvar type))
  : res (list (ident * globvar type)) := 
  let (id, gv) := const in
  do inits <- trans_init_datas (gvar_init gv) sconsts;
  let const1 := (id, mkglobvar (gvar_info gv) inits (gvar_readonly gv) (gvar_volatile gv)) in
  OK (sconsts ++ const1 :: nil).

Fixpoint trans_gconsts (consts sconsts : list (ident * globvar type))
  : res (list (ident * globvar type)) :=  
  match consts with
  | nil => OK sconsts
  | const :: const_rest =>
    do sconsts1 <- trans_gconst const sconsts;
    trans_gconsts const_rest sconsts1
  end.
     
Definition trans_program(p: program) : res (program) :=
  do const_block1 <- trans_gconsts (const_block p) nil;
  OK (mkprogram (type_block p) const_block1 (node_block p) (node_main p)).


Lemma trans_program_ids_range:
  forall p p',
  trans_program p = OK p' ->
  ids_range ACG_B (node_block p) ->
  ids_range ACG_B (node_block p').
Proof.
  red; intros. 
  monadInv H. simpl in *. auto.
Qed.

Lemma  trans_gconst_ids:
  forall a init l,
  trans_gconst a init = OK l ->
  map fst l = map fst init ++ fst a :: nil.
Proof.
  destruct a; simpl; intros; auto.
  monadInv H. rewrite map_app. simpl. auto.
Qed.

Lemma  trans_gconsts_ids:
  forall l init l',
  trans_gconsts l init = OK l' ->
  map fst l' = map fst init ++ map fst l.
Proof.
  induction l; simpl; intros.
  rewrite <-app_nil_end. inv H. auto.
  monadInv H. rewrite IHl with x l'; auto.
  rewrite trans_gconst_ids with a init x; auto.
  rewrite app_ass. auto.
Qed.

Lemma trans_program_gids_range:
  forall id p p',
  trans_program p = OK p' ->
  ids_plt id (globidspltof p) ->
  ids_plt id (globidspltof p').
Proof.
  red; intros. apply in_app_or in H1. apply H0. apply in_or_app.
  monadInv H. simpl in *. destruct H1.
  left. apply trans_gconsts_ids in EQ.
  simpl in *. congruence.
  right. auto.
Qed.