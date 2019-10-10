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

(** Translate pre in LustreS. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Floats.
Require Import Errors.
Require Import Cop.
Require Import Lident.
Require Import Ctypes.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import Toposort.
Require Import LustreS.
Require Import Permutation.

Local Open Scope error_monad_scope.

Record generator : Type := mkgenerator {
  pre_next: ident;
  pre_types: list (ident * type)
}.

Fixpoint in_types(ty: type)(l: list type): bool :=
  match l with
  | nil => false
  | t :: l' => 
    if type_compare ty t then true else in_types ty l'
  end.

Fixpoint find_type(ty: type)(l: list (ident*type)) : res (ident*type) :=
  match l with
  | nil => Error (msg"SimplLustreS.find_type: ty not found in pre_types") 
  | (id,t)::tl => 
    if type_compare ty t then OK (id,t) else find_type ty tl
  end.

Fixpoint filter_types(l tys: list type): list type :=
  match l with
  | nil => tys
  | ty :: l' =>
    if in_types ty tys then 
      filter_types l' tys
    else
      filter_types l' (tys ++ ty :: nil)
  end.

Definition pretypeof_stmt(s: stmt): list type:=
  match s with
  | Spre lh id a1 => 
    if is_arystr (typeof a1) then (typeof a1 :: nil) else nil
  | Scurrent lh id a a1 =>
    if is_arystr (typeof a1) then (typeof a1 :: nil) else nil
  | _ => nil
  end.

Definition pretypeof_stmts(ss:list (stmt*clock)): list type:=
  flat_map pretypeof_stmt (map fst ss).

Definition pretypeof_node(nd: ident*node): list type:=
  pretypeof_stmts (nd_stmt (snd nd)).

Fixpoint gen_pre_types(l: list type)(g: generator): generator :=
  match l with
  | nil => g
  | ty :: l' =>
    let constid := acg_init_pre_name (pre_next g) in
    let g1 := mkgenerator (Psucc (pre_next g)) (pre_types g++(constid, ty)::nil) in
    gen_pre_types l' g
  end.

Fixpoint check_pre_types(l: list type): bool:=
  match l with
  | nil => true
  | ty :: l' =>
    if zlt 0 (sizeof ty) && zle (sizeof ty) Int.max_signed then
      check_pre_types l'
    else false
  end.

Definition gen_pre_exp(ty: type)(tys: list (ident*type)): res sexp :=
  match ty with
  | Tstruct _ _ | Tarray _ _ _ =>
    do (constid, t) <- find_type ty tys; 
    OK (Svar constid ty)
  | Tfloat F32 => OK (Sconst (Csingle Float32.zero) ty)
  | Tfloat F64 => OK (Sconst (Cfloat Float.zero) ty)
  | Tint Tbool _ => OK (Sconst (Cbool false) ty) 
  | _ => OK (Sconst (Cint Int.zero) ty)
  end.

Definition trans_stmt(tys: list (ident*type))(s: stmt): res stmt:=
  match s with
  | Spre lh id a1 =>
    do a2 <- gen_pre_exp (typeof a1) tys;
    OK (Sfby lh id a1 a2)
  | Scurrent lh id a a1 =>
    do a2 <- gen_pre_exp (typeof a1) tys;
    OK (ScurrentR lh id a a1 a2)
  | _ => OK s 
  end.

Definition trans_stmtclock(tys: list (ident*type))(sc: stmt*clock): res (stmt*clock):=
  do s <- trans_stmt tys (fst sc);
  OK (s, snd sc).

Definition trans_body(tys: list (ident*type))(b: node): res node :=
  do s <- mmap (trans_stmtclock tys) b.(nd_stmt);
  if list_in_list (map fst tys) (map fst (mkloopmapw (nd_stmt b) ++ allvarsof b)) then
    Error (msg "SimplLustreS: pre_const names are in local names!")
  else
    OK (mknode b.(nd_kind) b.(nd_args) b.(nd_rets) b.(nd_flags) b.(nd_svars) b.(nd_vars) 
      s b.(nd_sid) b.(nd_fld) b.(nd_eqt)).

Definition trans_node(tys: list (ident*type))(f: ident*node): res (ident*node) :=
  do b <- trans_body tys (snd f);
  OK (fst f, b).

Definition gen_pre_const(it: ident*type): ident * globvar type :=
  let v := Init_space (sizeof (snd it)) :: nil in 
  (fst it, mkglobvar (snd it) v true true).

Definition pretypeof_prog(p: program): (list (ident*type)) :=
  let tys := flat_map pretypeof_node (node_block p) in
  let tys' := filter_types tys nil in 
  let g := gen_pre_types tys' (mkgenerator xH nil) in
  pre_types g.

Definition trans_program(p: program): res (program) :=
  let pretys := pretypeof_prog p in
  let pre_consts := map gen_pre_const pretys in
  do nodes <- mmap (trans_node pretys) (node_block p);
  if list_in_list (map fst pretys) (globidsof p) then
    Error (msg "SimplLustreS: pre_const names are in global names!")
  else
    if check_norepeat (map fst pretys) then
      if names_plt ACG_EQU (map fst pretys) then
        if check_pre_types (map snd pretys) then
          OK (mkprogram (type_block p) (const_block p ++ pre_consts) nodes (node_main p))
        else
          Error (msg "SimplLustreS: sizeof pretypes are overflow!")
      else
        Error (msg "SimplLustreS: pre_const names are in local temp names!")
    else Error (msg "SimplLustreS: pre_const names names are repeated!").

Lemma find_type_in:
  forall tys ty id t,
  find_type ty tys = OK (id, t) ->
  In (id, t) tys.
Proof.
  induction tys; simpl; intros; try congruence.
  destruct a. destruct (type_compare _ _) eqn:?.
  inv H; auto.
  right. eapply IHtys; eauto.
Qed.

Lemma find_type_eq:
  forall tys ty id t,
  find_type ty tys = OK (id, t) ->
  ty  = t.
Proof.
  induction tys; simpl; intros; try congruence.
  destruct a. destruct (type_compare _ _) eqn:?.
  inv H. eapply type_compare_eq; eauto.
  eapply IHtys; eauto.
Qed.
    
Lemma trans_stmts_get_stmt_nid:
  forall l tys l',
  mmap (trans_stmtclock tys) l = OK l' ->  
  flat_map get_stmt_nid l = flat_map get_stmt_nid l'.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  monadInv H.
  erewrite IHl; eauto. simpl. f_equal. destruct a.
  unfold trans_stmtclock in *. monadInv EQ.
  destruct s; inv EQ0; simpl in *; auto.
  monadInv H0. auto.
  monadInv H0. auto.
Qed.

Lemma trans_nodes_deps_of_nodes_simpl:
  forall l tys l',
  mmap (trans_node tys) l = OK l' ->
  deps_of_nodes_simpl l = deps_of_nodes_simpl l'.
Proof.
  induction l; simpl; intros.
  inv H. auto.
  monadInv H. erewrite IHl; simpl; eauto. f_equal.
  monadInv EQ. monadInv EQ0.
  destruct (list_in_list _ _) eqn:?; try congruence.
  inv EQ2. simpl.
  erewrite trans_stmts_get_stmt_nid; eauto.
Qed.

Lemma trans_stmts_svars_eq:
  forall l tys l',
  mmap (trans_stmtclock tys) l = OK l' ->  
  clocksof l = clocksof l' /\ fbyvarsof l = fbyvarsof l' /\ instidof l = instidof l'.
Proof.
  induction l; simpl; intros.
  inv H; auto.
  monadInv H. simpl in *.
  apply IHl in EQ1. destruct EQ1 as [? [? ?]].
  rewrite H, H0, H1.
  monadInv EQ. destruct a.
  destruct s; inv EQ0; simpl; auto.
  monadInv H3; auto.
  monadInv H3; auto.
Qed.

Lemma trans_program_ids_range:
  forall p p', ids_range ACG_B (node_block p) ->
  trans_program p = OK p' ->
  ids_range ACG_B (node_block p').
Proof.
  unfold ids_range, ids_range, trans_program. intros.
  monadInv H0.
  destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _) eqn:?; try congruence.
  destruct (check_pre_types _) eqn:?; try congruence. 
  inv EQ0. simpl in *.
  eapply in_mmap_iff in EQ; eauto.
  destruct EQ as [? [? ?]].
  apply H in H2. monadInv H0. monadInv EQ.
  destruct (list_in_list _ (map fst (mkloopmapw (nd_stmt (snd x0)) ++ allvarsof (snd x0)))) eqn:?; try congruence.
  inv EQ1. unfold allidsof, predidof, allvarsof in *. simpl in *.
  apply trans_stmts_svars_eq in EQ0. destruct EQ0 as [? [? ?]].
  rewrite <-H0, <-H3, <-H4; auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p p',
  trans_program p = OK p' ->
  list_norepet (globidsof p) ->
  list_norepet (globidsof p').
Proof.
  unfold trans_program, globidsof. intros.
  monadInv H.
  destruct (list_in_list _ _) eqn:?; try congruence.
  apply list_in_list_disjoint in Heqb; auto.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _); try congruence.
  destruct (check_pre_types _) eqn:?; inv EQ0.
  simpl in *. 
  remember (pretypeof_prog _).
  rewrite <-trans_nodes_fids_eq with (l1:= (node_block p)) (f:=trans_node l); auto.
  apply list_norepet_permut with 
        (map fst (map gen_pre_const l) ++ ((map fst (type_block p) ++ map fst (const_block p)) ++ map fst (node_block p))); auto.
  +apply list_norepet_app; auto. repeat (split; auto).
   apply check_norepeat_list_norepet in Heqb0; auto.
   rewrite map_map. auto.
   rewrite map_map. simpl. auto.
  +repeat rewrite map_app.
   repeat rewrite <-app_ass. apply Permutation_app_tail.
   apply Permutation_trans with 
        (map fst (map gen_pre_const l)
         ++ (((map fst (type_block p)) ++ map fst (const_block p)))); auto.
   -repeat rewrite app_ass. apply Permutation_refl. 
   -apply Permutation_app_swap.
  +intros. monadInv H. auto.
Qed.

Lemma trans_program_deps_of_nodes_simpl:
  forall p p',
  trans_program p = OK p' ->
  deps_of_nodes_simpl (node_block p) = deps_of_nodes_simpl (node_block p').
Proof.
  unfold trans_program. intros.
  monadInv H.
  destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _) eqn:?; try congruence.
  destruct (check_pre_types _) eqn:?; try congruence. 
  inv EQ0. simpl.
  eapply trans_nodes_deps_of_nodes_simpl; eauto.
Qed.

Lemma trans_program_ids_plt:
  forall p p',
  trans_program p = OK p' ->
  ids_plt ACG_EQU (globidspltof p) ->
  ids_plt ACG_EQU (globidspltof p').
Proof.
  unfold trans_program, globidspltof. intros.
  monadInv H.
  destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _) eqn:?; try congruence.
  destruct (check_pre_types _) eqn:?; try congruence. 
  inv EQ0. simpl.
  red. intros. remember (pretypeof_prog _).
  rewrite map_app in H. apply in_app_or in H. destruct H.
  apply in_app_or in H. destruct H.
  apply H0. apply in_or_app; auto.
  eapply names_plt_ids_plt in Heqb1; eauto.
  apply Heqb1. rewrite map_map in H. auto.
  apply H0. rewrite trans_nodes_fids_eq with (l2:=x) (f:=trans_node l); auto.
  apply in_or_app; auto.
  intros. monadInv H1; auto.
Qed.
  