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
Require Import AST.
Require Import Errors.
Require Import Maps.
Require Import Integers.
Require Import List.
Require Import Permutation.
Require Import Lident.
Require Import Lustre.
Require Import LustreS.
Require Import Toposort.
Require Import ExtraList.
Require Import Ltypes.
Require Import Lvalues.
Require Import Lenv.
Require Import Lenvmatch.
Require Import Lsem.
Require Import LsemT.

Section CORRECTNESS.

Variable prog: program.
Variable gc: locenv.

Hypothesis TOPOSORTED:
  forall fd, In fd (node_block prog) -> 
  topo_sorted (deps_of_stmts (nd_stmt (snd fd))).

Lemma eval_toposorted_stmts_correct:
  forall nid nk te1 te2 e1 e2 ss f,
  ids_norepet f ->
  stmts_topo_match (nd_stmt f) ss ->
  In (nid, f) (node_block prog) ->
  eval_stmts false prog gc nk te1 e1 te2 e2 ss ->
  eval_stmts false prog gc nk te1 e1 te2 e2 (nd_stmt f).
Proof.
  intros. destruct H0 as [A [A1 A2]].
  destruct H as [? [? ?]].
  apply list_norepet_app in H0. destruct H0 as [? [? ?]].
  eapply eval_index_stmts_correct; eauto.
  +eapply topo_sorted_eqs_simpl; eauto.
  +apply Permutation_sym; auto.
  +eapply topo_sorted_eqs_simpl; eauto.
   apply TOPOSORTED in H1; auto.
  +apply list_norepet_permut with (map instid (instidof (nd_stmt f))); auto.
   apply Permutation_map. apply flat_map_permutation; auto.
  +eapply list_norepet_permut in H0; eauto. 
   apply Permutation_map. apply Permutation_app.
   apply clockvarsof_permut_map; auto.
   apply flat_map_permutation; auto.
   apply flat_map_permutation; auto.
Qed.

Lemma eval_node_correct:
  forall e e' fd vargs vrets,
  eval_node true prog gc e e' fd vargs vrets ->
  In fd (node_block prog) ->
  eval_node false prog gc e e' fd vargs vrets.
Proof.
  intros until vrets.
  induction 1 using eval_node_ind2 with  
  (P0:= fun nk te e te' e' ss => 
     eval_stmts false prog gc nk te e te' e' ss)
  (P1:= fun nk te e te' e' s ta1 ta2 =>
     eval_stmt false prog gc nk te e te' e' s  ta1 ta2)
  (P2:= fun nk te e te' e' f ta1 => 
     eval_hstmt false prog gc nk te e te' e' f ta1)
  ( P3 := fun nk se se1 atys vargs i cdef rtys vrets => 
      eval_apply false prog gc nk se se1 atys vargs i cdef rtys vrets); 
   simpl; intros; try (econstructor; eauto; fail).
 +(*node*)
  apply exec_node with te te1 te2 eh1 (nd_stmt f); auto.
  -eapply eval_toposorted_stmts_correct; eauto.
  -destruct H2 as [A [A1 A2]].
   eapply eval_eqtsof_permut in H4; eauto.
   apply Permutation_sym; auto.
   eapply list_norepet_permut with (map fst (map fst (clockvarsof (clocksof (nd_stmt f)))++ fbyvarsof (nd_stmt f))); eauto.    
   apply ids_norepet_clockfbyids_norepet; auto.
   apply Permutation_map. apply Permutation_app.
   apply clockvarsof_permut_map; auto.
   apply flat_map_permutation; auto.
   apply flat_map_permutation; auto.
   apply clockvarsof_permut; auto.
   apply flat_map_permutation; auto.
   apply Permutation_sym; auto.
   apply clocks_determ_permut with (clocksof (nd_stmt f)); auto.
   apply flat_map_permutation; auto.
 +econstructor 3; eauto.
 +apply eval_Sfby_cycle_n with v1 v; auto.
 +apply eval_Sfbyn_cycle_n with sa aty v1 v; auto.
 +eapply eval_Scurrent_false; eauto.
 +eapply eval_Spre_cycle_n; eauto.
 +eapply eval_ScurrentR_false; eauto.
 +eapply eval_Hboolred_false; eauto.
 +econstructor; eauto.
  destruct H0. apply IHeval_node; auto.
  eapply find_funct_in2; eauto.
Qed.

Theorem exec_prog_correct_general:
  forall e main vass vrss n maxn,
  exec_prog prog gc (eval_node true) main e n maxn vass vrss ->
  In main (node_block prog) ->
  exec_prog prog gc (eval_node false) main e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
  +apply eval_node_correct in H0; auto.
   constructor 2 with e'; auto.
Qed.

Theorem exec_prog_correct:
  forall e main vass vrss n maxn,
  initial_state prog gc init_node main e ->
  exec_prog prog gc (eval_node true) main e n maxn vass vrss ->
  exec_prog prog gc (eval_node false) main e n maxn vass vrss.
Proof.
  intros. apply exec_prog_correct_general; auto.
  inv H; eapply find_funct_in2; eauto.
Qed.

End CORRECTNESS.  


