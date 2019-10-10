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

(** Translation from LustreS to LustreS. *)

Require Import Coqlib.
Require Import Ctypes.
Require Import Cltypes.
Require Import AST.
Require Import Errors.
Require Import List.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Memdata.
Require Import Globalenvs.
Require Import Bool.
Require Import Lop.
Require Import ExtraList.
Require Import Lustre.
Require Import LustreS.
Require Import Lident.
Require Import Ltypes.
Require Import Cop.
Require Import Lvalues.
Require Import Lglobalenv.
Require Import Lenv.
Require Import Lsem.
Require Import LsemT.
Require Import SimplConstblock.

Section CORRECTNESS.

Variable prog1 prog2: program.

Hypothesis TRANS:
  trans_program prog1 = OK prog2.

Hypothesis GIDS_NOREPET:
  list_norepet (globidsof prog1).

Lemma trans_program_globids_norepet:
  list_norepet (globidsof prog2).
Proof.
  intros. monadInv TRANS.
  apply trans_gconsts_ids in EQ. simpl in *.
  unfold globidsof in *. simpl in *.
  congruence.
Qed.

Lemma trans_node_call_func:
  forall c fd, call_func (node_block prog1) c fd ->
  call_func (node_block prog2) c fd.
Proof.
  unfold call_func. intuition.
  monadInv TRANS. auto.
Qed.

Lemma eval_node_correct:
  forall gc e e' fd vargs vrets,
  eval_node true prog1 gc e e' fd vargs vrets ->
  eval_node true prog2 gc e e' fd vargs vrets.
Proof.
  intros until vrets.
  induction 1 using eval_node_ind2 with  
  (P0:= fun nk te e te' e' ss => 
     eval_stmts true prog2 gc nk te e te' e' ss)
  (P1:= fun nk te e te' e' s ta1 ta2 =>
     eval_stmt true prog2 gc nk te e te' e' s ta1 ta2)
  (P2:= fun nk te e te' e' f ta1 =>
     eval_hstmt true prog2 gc nk te e te' e' f ta1)
  ( P3 := fun nk se se1 atys vargs i cdef rtys vrets =>
     eval_apply true prog2 gc nk se se1 atys vargs i cdef rtys vrets); simpl; intros;
  try (econstructor; eauto; fail).
  +econstructor 3; eauto.
  +eapply eval_Sfby_cycle_n; eauto.
  +eapply eval_Sfbyn_cycle_n; eauto.
  +eapply eval_Scurrent_false; eauto.
  +eapply eval_Spre_cycle_n; eauto.
  +eapply eval_ScurrentR_false; eauto.
  +eapply eval_Hboolred_false; eauto.
  +econstructor 1; eauto. 
   eapply trans_node_call_func; eauto.
Qed.

Theorem exec_prog_correct_general:
  forall gc e main vass vrss n maxn,
  exec_prog prog1 gc (eval_node true) main e n maxn vass vrss ->
  exec_prog prog2 gc (eval_node true) main e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
  +apply eval_node_correct in H0; auto.
   constructor 2 with e'; auto.
Qed.

Lemma init_node_correct:
  forall e fd,
  init_node prog1 e fd ->
  init_node prog2 e fd.
Proof.
  intros until fd.
  induction 1 using init_node_ind2 with 
  ( P0 := fun e1 e2 l =>
      init_stmt prog2 e1 e2 l
   ); intros.
 +(*init_node*)
  constructor 1; auto.
 +(*nil*)
  constructor.
 +(*cons*)
  constructor 2 with se1 fd ef; auto.
  eapply trans_node_call_func; eauto. 
Qed.

Lemma init_data_list_size_match:
  forall init gc gc' i m t gv,
  alloc_globals gc init = Some gc' ->
  gc ! i = None ->
  gc' ! i = Some (m, t) ->
  In (i, gv) init ->
  list_norepet (map fst init) ->
  Genv.init_data_list_size (gvar_init gv) = Z.of_nat (length m).
Proof.
  induction init; simpl; intros.
  +inv H. congruence.
  +destruct (alloc_global _ _) eqn:?; try congruence.
   inv H3. destruct H2.
   -subst. simpl in *. destruct gv.
    destruct (store_zeros _ _) eqn:?; try congruence.
    destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
    rewrite alloc_globals_notin_eq with (l:=init) (gc:=PTree.set i (m1, gvar_info) gc) in H1; auto.
    rewrite PTree.gss in H1; auto. inv H1.
    simpl. apply store_zeros_length in Heqo0.
    unfold alloc in Heqo0. rewrite length_list_repeat in Heqo0.
    apply store_init_datas_length in Heqo1.
    rewrite Heqo1, Heqo0.
    rewrite nat_of_Z_eq; auto.
    apply Genv.init_data_list_size_pos.
   -eapply IHinit; eauto.
    destruct a. destruct g. simpl in *.
    destruct (store_zeros _ _) eqn:?; try congruence.
    destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
    rewrite PTree.gso; auto. apply in_map with (f:=fst) in H2.
    simpl in H2. red; intros. subst. auto.
Qed.

Lemma genv_init_data_list_size_app:
  forall l1 l2 z1 z2,
  Genv.init_data_list_size l1 = z1 ->
  Genv.init_data_list_size l2 = z2 ->
  Genv.init_data_list_size (l1 ++ l2) = z1 + z2.
Proof.
  induction l1; simpl; intros.
  subst. omega.
  erewrite IHl1; eauto. omega.
Qed.

Lemma store_init_datas_trans:
  forall l1 l2 m m1 m' z,
  store_init_datas m z l1 = Some m1 ->
  store_init_datas m1 (z+Genv.init_data_list_size l1) l2 = Some m' ->
  store_init_datas m z (l1++l2) = Some m'.
Proof.
  induction l1; simpl; intros.
  +inv H. rewrite Z.add_0_r in H0. auto.
  +destruct (store_init_data _ _ _) eqn:?; try congruence.
   eapply IHl1; eauto.
   rewrite <-H0. f_equal. omega.
Qed.

Lemma init_datas_type_find:
  forall a gv,
  init_data_type a ->
  find_init_data gv a = Some (a::nil).
Proof.
  destruct a; simpl; intros; auto.
  destruct H.
Qed.

Lemma init_datas_types_find:
  forall l gv,
  init_data_types l ->
  find_init_datas gv l = Some l.
Proof.
  induction l; simpl; intros; auto.
  inv H.
  rewrite init_datas_type_find; auto.
  rewrite IHl; auto.
Qed.

Lemma alloc_globals_find_funct:
  forall init gc gc' gv gv' i l,
  Lglobalenv.alloc_globals gc gv init = Some (gc', gv') ->
  gv ! i = None ->
  gv' ! i = Some l ->
  list_norepet (map fst init) ->
  init_data_types (flat_map (fun x => AST.gvar_init (snd x)) init) ->
  exists v, find_funct init i = Some (i, v)
    /\ gvar_init v = l.
Proof.  
  induction init; simpl; intros.
  +inv H. congruence.
  +inv H2. destruct (Lglobalenv.alloc_global gc gv a) eqn:?; try congruence.
   destruct p as [gc0 gv0].
   destruct (identeq (fst a) i) eqn:?.
   -apply Pos.eqb_eq in Heqb. subst.
    destruct a; simpl in *.
    exists g. split; auto.
    destruct g. simpl.
    destruct (find_init_datas _ _) eqn:?; try congruence.
    destruct (store_zeros _ _) eqn:?; try congruence.
    destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
    erewrite alloc_globals_notin_eq_right in H1; eauto.
    rewrite PTree.gss in H1; auto. inv H1.
    rewrite init_datas_types_find in Heqo0; auto.
    inv Heqo0. auto.
    simpl in *.
    apply Forall_app in H3. intuition.
   -apply Pos.eqb_neq in Heqb.
    eapply IHinit; eauto.
    destruct a; simpl in *.
    destruct g. destruct (find_init_datas _ _) eqn:?; try congruence.
    destruct (store_zeros _ _) eqn:?; try congruence.
    destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
    rewrite PTree.gso; auto.
    apply Forall_app in H3. intuition.
Qed.

Lemma find_init_data_trans:
  forall gc gv a l init,
  find_init_data gv a = Some l ->
  Lglobalenv.alloc_globals empty_locenv empty_globalenv init = Some (gc, gv) ->
  list_norepet (map fst init) ->
  init_data_types (flat_map (fun x => AST.gvar_init (snd x)) init) ->
  trans_init_data a init = OK l.
Proof.
  destruct a; simpl; intros; inv H; auto.
  eapply alloc_globals_find_funct in H0; eauto.
  destruct H0 as [? [? ?]].
  apply find_funct_get_nt_byid in H.
  rewrite H. simpl. rewrite H0. auto.
  rewrite PTree.gempty. auto.
Qed.

Lemma find_init_datas_trans:
  forall gc gv l l' init,
  find_init_datas gv l = Some l' ->
  Lglobalenv.alloc_globals empty_locenv empty_globalenv init = Some (gc, gv) ->
  list_norepet (map fst init) ->
  init_data_types (flat_map (fun x => AST.gvar_init (snd x)) init) ->
  trans_init_datas l init = OK l'.
Proof.
  induction l; simpl; intros.
  +inv H. auto.
  +destruct (find_init_data _ _) eqn:?; try congruence.
   destruct (find_init_datas _ _) eqn:?; inv H.
  erewrite find_init_data_trans; eauto. 
  simpl. erewrite IHl; eauto. 
  simpl. auto.
Qed.

Lemma alloc_global_match:
  forall a a' init gc gc' gv gv',
  Lglobalenv.alloc_global gc gv a = Some (gc', gv') ->
  trans_gconst a init = OK (init++a'::nil) ->
  Lglobalenv.alloc_globals empty_locenv empty_globalenv init = Some (gc, gv) ->
  list_norepet (map fst init) ->
  init_data_types (flat_map (fun x => AST.gvar_init (snd x)) init) ->
  alloc_global gc a' = Some gc'.
Proof.
  destruct a; simpl; intros.
  destruct g. destruct (find_init_datas _ _) eqn:?; try congruence.
  destruct (store_zeros _ _) eqn:?; try congruence.
  destruct (store_init_datas _ _ _) eqn:?; try congruence.
  inv H. monadInv H0.
  apply app_inv_head in H0.
  inv H0. simpl in *.
  erewrite find_init_datas_trans in EQ; eauto.
  inv EQ. rewrite Heqo0. rewrite Heqo1. auto.
Qed.

Lemma find_init_datas_app:
  forall gv l1 l2 l3 l4,
  find_init_datas gv l1 = Some l3 ->
  find_init_datas gv l2 = Some l4 ->
  find_init_datas gv (l1 ++ l2) = Some (l3 ++ l4).
Proof.
  induction l1; simpl; intros.
  inv H; auto.
  destruct (find_init_data gv a) eqn:?; try congruence.
  destruct (find_init_datas _ l1) eqn:?; try congruence.
  inv H. erewrite IHl1; eauto.
  rewrite app_ass; auto.
Qed.

Lemma trans_init_data_types:
  forall a l init,
  trans_init_data a init = OK l ->
  init_data_types (flat_map (fun x => gvar_init (snd x)) init) ->
  init_data_types l.
Proof.
  destruct a; intros; inv H; 
  try constructor; simpl; auto.
  monadInv H2.
  apply find_funct_get_nt_byid in EQ.
  apply find_funct_in2 in EQ.
  apply flat_map_in with (f:=fun x => gvar_init (snd x)) in EQ.
  simpl in *. apply Forall_forall. intros.
  apply EQ in H. eapply Forall_forall in H0; eauto.
Qed.

Lemma trans_init_datas_types:
  forall l l' init,
  trans_init_datas l init = OK l' ->
  init_data_types (flat_map (fun x => gvar_init (snd x)) init) ->
  init_data_types l'.
Proof.
  induction l; simpl; intros.
  inv H. constructor.
  monadInv H. red. 
  apply trans_init_data_types in EQ; auto.
  apply IHl in EQ1; auto.
  apply Forall_app; auto.
Qed.

Lemma global_alloc_global_match:
  forall a a' init gc gc' gv gv',
  Lglobalenv.alloc_global gc gv a = Some (gc', gv') ->
  trans_gconst a init = OK (init++a'::nil) ->
  Lglobalenv.alloc_globals empty_locenv empty_globalenv init = Some (gc, gv) ->
  list_norepet (map fst init) ->
  init_data_types (flat_map (fun x => AST.gvar_init (snd x)) init) ->
  Lglobalenv.alloc_global gc gv a' = Some (gc', gv').
Proof.
  destruct a; simpl; intros.
  destruct g. destruct (find_init_datas _ _) eqn:?; try congruence.
  destruct (store_zeros _ _) eqn:?; try congruence.
  destruct (store_init_datas _ _ _) eqn:?; try congruence.
  inv H. monadInv H0. apply app_inv_head in H0.
  inv H0. simpl in *.
  rewrite init_datas_types_find; auto.
  erewrite find_init_datas_trans in EQ; eauto.
  inv EQ. rewrite Heqo0. rewrite Heqo1; auto.
  eapply trans_init_datas_types; eauto.
Qed.

Lemma trans_gconst_exists:
  forall a init l,
  trans_gconst a init = OK l ->
  exists a', l = init ++ a' :: nil.
Proof.
  destruct a; simpl; intros.
  monadInv H. eauto.
Qed.

Lemma trans_gconsts_exists:
  forall l init l',
  trans_gconsts l init = OK l' ->
  exists l1, l' = init ++ l1.
Proof.
  induction l; simpl; intros.
  inv H. exists nil. rewrite app_nil_r; auto.
  monadInv H. eapply trans_gconst_exists in EQ; eauto.
  destruct EQ. subst x.
  apply IHl in EQ0. destruct EQ0. 
  subst l'. exists (x0::x). rewrite app_ass. auto.
Qed.

Lemma alloc_globals_match:
  forall l l' init gc gc' gv gv',
  Lglobalenv.alloc_globals gc gv l = Some (gc', gv') ->
  trans_gconsts l init = OK (init++l') ->
  Lglobalenv.alloc_globals empty_locenv empty_globalenv init = Some (gc, gv) ->
  list_norepet (map fst (init++l)) ->
  init_data_types (flat_map (fun x => AST.gvar_init (snd x)) init) ->
  alloc_globals gc l' = Some gc'.
Proof.
  induction l; simpl; intros.
  +inv H. destruct l'. auto.
   rewrite <-app_nil_r with (l:=init) in H0 at 1.
   inversion H0. apply app_inv_head in H4. congruence.
  +destruct (Lglobalenv.alloc_global gc gv a) eqn:?; try congruence.
   destruct p as [gc0 gv0]. monadInv H0.
   destruct trans_gconst_exists with a init x as [a' A]; auto.
   subst x.
   destruct trans_gconsts_exists with l (init ++ a' :: nil) (init++l') as [l1 A]; auto.
   rewrite app_ass in A. apply app_inv_head in A.
   subst l'. simpl.
   cut (list_norepet (map fst init)). intros A1.
   erewrite alloc_global_match; eauto.
   eapply IHl with (init:=init++a'::nil); eauto.
   rewrite app_ass; auto.
   -eapply Lglobalenv.alloc_globals_app; eauto.
    simpl. erewrite global_alloc_global_match; eauto.
   -destruct a; simpl in *; auto.
    monadInv EQ. repeat rewrite map_app in *. simpl in *.
    rewrite app_ass. auto.
   -unfold trans_gconst in EQ. destruct a.
    monadInv EQ. rewrite flat_map_app. simpl. rewrite app_nil_r.
    apply Forall_app; auto. split; auto.
    eapply trans_init_datas_types; eauto.
   -rewrite map_app in H2. apply list_norepet_app in H2.
    intuition.
Qed.

Lemma trans_gconsts_init_genvc_match:
  forall l l' gc gv,
  Lglobalenv.init_genvc l = Some (gc, gv) ->
  trans_gconsts l nil = OK l' ->
  list_norepet (map fst l) ->
  init_genvc l' = Some gc.
Proof.
  unfold init_genvc. intros.
  rewrite <-app_nil_l with (l:=l') in H0.
  eapply alloc_globals_match; eauto.
  simpl. constructor.
Qed.

Lemma initial_states_match:
  forall gc main e,
  Lglobalenv.initial_state prog1 gc init_node main e ->
  initial_state prog2 gc init_node main e.
Proof.
  intros. inv H.
  constructor 1; simpl; auto.
  +monadInv TRANS. simpl.
   eapply trans_gconsts_init_genvc_match; eauto.
   unfold globidsof in GIDS_NOREPET.
   apply list_norepet_app in GIDS_NOREPET.
   intuition. apply list_norepet_app in H.
   intuition.
  +monadInv TRANS. auto.
  +apply init_node_correct; auto.
Qed.

Theorem trans_program_correct:
  forall gc e main vass vrss maxn,
  Lglobalenv.initial_state prog1 gc init_node main e->
  exec_prog prog1 gc (eval_node true) main e 1 maxn vass vrss ->
  initial_state prog2 gc init_node main e
    /\ exec_prog prog2 gc (eval_node true) main e 1 maxn vass vrss.
Proof.
  intros.
  apply initial_states_match in H.
  split; auto.
  eapply exec_prog_correct_general; eauto.
Qed.

End CORRECTNESS.  

