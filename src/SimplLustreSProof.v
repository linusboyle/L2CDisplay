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
Require Import Maps.
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
Require Import LustreS.
Require Import Lvalues.
Require Import Lenv.
Require Import LsemT.
Require Import Lsem.
Require Import Lenvmatch.
Require Import LsemS.
Require Import SimplLustreS.

Section CORRECTNESS.

Variable prog1 prog2: program.

Hypothesis TRANS:
  trans_program prog1 = OK prog2.

Definition pre_types_match(tys: list (ident*type))(gc: locenv) : Prop :=
  forall id t m, In (id, t) tys ->
  eval_pre t (Vmvl m) ->
  gc ! id = Some (m, t) /\ sizeof t = Z.of_nat (length m).

Definition pre_types_sizeof(tys: list (ident*type)) : Prop :=
  forall id t, In (id, t) tys ->
  0 < sizeof t <= Int.max_signed.

Lemma check_pre_types_sizeof:
  forall l,
  check_pre_types (map snd l) = true ->
  pre_types_sizeof l.
Proof.
  induction l; simpl; intros.
  red; simpl; intros; tauto.
  destruct (zlt _ _), (zle _ _); inv H.
  red; simpl; intros.
  destruct H.
  subst; simpl in *; try omega.
  apply IHl in H; auto.
Qed.
  
Lemma pre_types_sizeof_prog1:
  pre_types_sizeof (pretypeof_prog prog1).
Proof.
  monadInv TRANS.
  destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _) eqn:?; try congruence.
  destruct (check_pre_types _) eqn:?; try congruence.
  apply check_pre_types_sizeof; auto.
Qed.

Lemma alloc_globals_match:
  forall tys gc gc',
  alloc_globals gc (map gen_pre_const tys) = Some gc' ->
  list_norepet (map fst tys) ->
  pre_types_match tys gc'.
Proof.
  induction tys; simpl; intros.
  +inv H. red; simpl; intros. tauto.
  +rewrite Zplus_0_r in H.
   generalize (sizeof_pos (snd a)). intros.
   rewrite Z.max_l in H; try omega.
   destruct (store_zeros _ _) eqn:?; try congruence.
   red. simpl. intros. inv H3. inv H0. destruct H2.
   -subst. simpl in *. rewrite Heqo in H6. inv H6. split.
    *erewrite alloc_globals_notin_eq; eauto.
     rewrite PTree.gss; auto.
     rewrite map_map; auto.
    *erewrite store_zeros_length; eauto. 
     rewrite length_alloc.
     rewrite nat_of_Z_eq; try omega.
   -apply IHtys in H; auto.
    destruct H with id t m0; auto.
    constructor; auto.
Qed.

Lemma type_block_eq:
  type_block prog2 = type_block prog1.
Proof.
  monadInv TRANS. 
  destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _) eqn:?; try congruence.
  destruct (check_pre_types _) eqn:?; try congruence. 
  inv EQ0; auto.
Qed.

Lemma gcenv_match_eval_var:
  forall gc1 t e i ofs k v,
  eval_var gc1 t e i ofs k v ->
  forall gc2, locenv_match gc1 gc2 ->
  eval_var gc2 t e i ofs k v.
Proof.
  induction 1; intros.
  constructor 1; auto.
  eapply load_env_match; eauto.
  constructor 2; auto.
Qed.

Lemma gcenv_match_eval_sexp:
  forall gc1 eh a v,
  eval_sexp gc1 eh a v ->
  forall gc2, locenv_match gc1 gc2 ->
  eval_sexp gc2 eh a v
with gcenv_match_eval_lvalue:
  forall gc1 eh s id ofs k,
  eval_lvalue gc1 eh s id ofs k ->
  forall gc2, locenv_match gc1 gc2 ->
  eval_lvalue gc2 eh s id ofs k.
Proof.
 +induction 1; simpl; intros;
  try (econstructor; eauto; fail).
  apply eval_Rlvalue with id ofs k; auto.
   eapply gcenv_match_eval_lvalue; eauto.
   eapply gcenv_match_eval_var; eauto.
 +induction 1; simpl; intros; econstructor; eauto.
Qed.
  
Lemma gcenv_match_eval_sexps:
  forall gc1 eh l vl,
  Forall2 (eval_sexp gc1 eh) l vl ->
  forall gc2, locenv_match gc1 gc2 ->
  Forall2 (eval_sexp gc2 eh) l vl.
Proof.
  induction 1; intros.
  constructor.
  constructor 2; auto.
  eapply gcenv_match_eval_sexp; eauto.
Qed.

Lemma gcenv_match_eval_typecmp:
  forall gc1 eh a1 a2 b,
  eval_typecmp gc1 eh a1 a2 b ->
  forall gc2, locenv_match gc1 gc2 ->
  eval_typecmp gc2 eh a1 a2 b.
Proof.
  intros until eh.
  induction 1 using eval_typecmp_ind2 with 
  ( P0 := fun a1 a2 num aty i b =>
      forall gc2, locenv_match gc1 gc2 ->
      eval_arycmp gc2 eh a1 a2 num aty i b)
  ( P1 := fun a1 a2 fld ftl b =>
      forall gc2, locenv_match gc1 gc2 ->
      eval_strcmp gc2 eh a1 a2 fld ftl b
  ); intros.
Proof.
 +constructor 1 with chunk v; auto.
  eapply gcenv_match_eval_sexp; eauto.
 +constructor 2 with aid aty num v1 v2; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
 +constructor 3 with sid fld v1 v2; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
 +constructor 1; auto.
 +constructor 2; auto.
 +constructor 1; auto.
 +constructor 2; auto.
Qed.

Lemma gcenv_match_eval_expr:
  forall gc1 te a ty v,
  eval_expr gc1 te a ty v ->
  forall gc2, locenv_match gc1 gc2 ->
  eval_expr gc2 te a ty v.
Proof.
  induction 1; intros.
 +constructor; auto.
  eapply gcenv_match_eval_sexp; eauto.
 +eapply eval_Earyprj_in; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexps; eauto.
 +eapply eval_Earyprj_out; eauto.
  eapply gcenv_match_eval_sexps; eauto.
  eapply gcenv_match_eval_sexp; eauto.
 +eapply eval_Ecase; eauto;
  eapply gcenv_match_eval_sexp; eauto.
 +eapply eval_Eif; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
 +eapply eval_Eprefix; eauto.
  eapply gcenv_match_eval_sexps; eauto.
 +eapply eval_Etypecmp; eauto.
  eapply gcenv_match_eval_typecmp; eauto.
 +eapply eval_Emerge; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
Qed.

Lemma gcenv_match_locenv_setlvar:
  forall gc1 te a v te',
  locenv_setlvar gc1 te a v te' ->
  forall gc2, locenv_match gc1 gc2 ->
  locenv_setlvar gc2 te a v te'.
Proof.
  induction 1; intros.
  constructor 1 with b ofs; auto.
  eapply gcenv_match_eval_lvalue; eauto.
Qed.

Lemma eval_pre_genper:
  forall ty v,
  eval_pre ty v ->
  forall tys a gc2 te, gen_pre_exp ty tys = OK a ->
  ptree_ids_none (map fst tys) te ->
  pre_types_match tys gc2 ->
  pre_types_sizeof tys ->
  eval_sexp gc2 te a v.
Proof.
  induction 1; intros; intros.
 +destruct ty; simpl in *; try congruence; inv H2.
  -monadInv H7.
   assert(x0 = Tarray i ty z).
     apply find_type_eq in EQ; auto.
   subst.
   assert(A: In (x, Tarray i ty z) tys).
     apply find_type_in in EQ; auto. 
   destruct H4 with x (Tarray i ty z) m as [? ?]; auto.
     constructor; auto.
   apply eval_Rlvalue with x Int.zero Gid; auto.
   *constructor 2 with m; auto.
    apply H3. apply in_map with (f:=fst) in A; auto.
   *constructor 1.
    exists m, (Tarray i ty z). repeat split; auto.
    constructor; auto.
    simpl typeof. rewrite H6. apply loadbytes_full; auto.
    rewrite <-H6. apply H5 with x; auto.
    rewrite Int.unsigned_zero. simpl. 
    exists 0. omega.
  -monadInv H7.
   assert(x0 = Tstruct i f).
     apply find_type_eq in EQ; auto.
   subst.
   assert(A: In (x, Tstruct i f) tys).
     apply find_type_in in EQ; auto. 
   destruct H4 with x (Tstruct i f) m as [? ?]; auto.
     constructor; auto.
   apply eval_Rlvalue with x Int.zero Gid; auto.
   *constructor 2 with m; auto.
    apply H3. apply in_map with (f:=fst) in A; auto.
   *constructor 1.
    exists m, (Tstruct i f). repeat split; auto.
    constructor; auto.
    simpl typeof. rewrite H6. apply loadbytes_full; auto.
    rewrite <-H6. apply H5 with x; auto.
    rewrite Int.unsigned_zero. simpl. 
    exists 0. omega.
  +simpl in H. inv H. constructor; simpl; auto.
  +simpl in H. inv H. constructor; simpl; auto.
  +simpl in H. inv H. constructor; simpl; auto.
Qed.

Lemma gen_pre_exp_typeof:
  forall t tys a,
  gen_pre_exp t tys = OK a ->
  typeof a = t.
Proof.
  intros.
  destruct t; inv H; auto. 
  destruct f; inv H1; auto. 
  monadInv H1; auto.
  monadInv H1; auto.
Qed.

Lemma gcenv_match_assign_disjoint:
  forall gc1 te a1 a2,
  assign_disjoint (eval_lvalue gc1 te) a1 a2 ->
  forall gc2, locenv_match gc1 gc2 -> 
  assign_disjoint (eval_lvalue gc2 te) a1 a2.
Proof.
  intros. inv H.
  constructor 1 with chunk; auto.
  constructor 2; auto.
  inv H2. constructor 1 with id1 id2 o1 o2 k1 k2; auto.
  eapply gcenv_match_eval_lvalue; eauto.
  eapply gcenv_match_eval_lvalue; eauto.
Qed. 

Lemma gcenv_match_eval_eqf:
  forall gc1 te te1 a,
  eval_eqf gc1 te te1 a ->
  forall gc2, locenv_match gc1 gc2 -> 
  eval_eqf gc2 te te1 a.
Proof.
  intros. inv H.
  constructor 1 with v v'; auto. 
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply gcenv_match_assign_disjoint; eauto.
Qed.

Lemma trans_stmtclocks_has_for:
  forall tys l l',
  mmap (trans_stmtclock tys) l = OK l' ->
  has_fors l = has_fors l'.
Proof.
  induction l; simpl; intros.
  inv H. auto.
  monadInv H. rewrite IHl with x0; auto.
  destruct a. monadInv EQ.
  destruct s; simpl in *; inv EQ0; auto.
  monadInv H0. auto.
  monadInv H0. auto.
Qed.

Lemma trans_body_ids_norepet:
  forall tys f f',
  trans_body tys f = OK f' ->
  ids_norepet f ->
  ids_norepet f'.
Proof.
  unfold trans_body, ids_norepet, allidsof, predidof, allvarsof.
  intros. monadInv H. 
  destruct (list_in_list _ _) eqn:?; try congruence. 
  inv EQ0. simpl.
  destruct trans_stmts_svars_eq with (nd_stmt f) tys x as [? [? ?]]; auto.
  rewrite <-H, <-H1, <-H2. auto.
Qed.

Lemma call_func_match:
  forall cdef fd,
  call_func (node_block prog1) cdef fd ->
  exists fd', trans_node (pretypeof_prog prog1) fd = OK fd'
    /\ call_func (node_block prog2) cdef fd'.
Proof.
  intros. inv H. monadInv TRANS. 
  destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _) eqn:?; try congruence.
  destruct (check_pre_types _) eqn:?; try congruence. 
  inv EQ0. eapply find_funcs_monad_exits in EQ; eauto.
  destruct EQ as [fd' [? ?]].
  exists fd'. split; auto. 
  constructor; auto.
  monadInv H. unfold trans_body in EQ.
  monadInv EQ; auto. unfold node in *.
  destruct (list_in_list _ (map fst (mkloopmapw (nd_stmt (snd fd)) ++ allvarsof (snd fd)))) eqn:?; try congruence.
  inv EQ1. auto. 
  intros. monadInv H. monadInv EQ0; auto.
Qed.

Lemma trans_stmtclocks_fbyeqsof:
  forall l l',
  mmap (trans_stmtclock (pretypeof_prog prog1)) l = OK l' -> 
  fbyeqsof l' = fbyeqsof l.
Proof. 
  induction l; simpl; intros.
  inv H. auto. 
  monadInv H. simpl.
  rewrite IHl; auto.
  destruct a. monadInv EQ. 
  destruct s; monadInv EQ0; simpl; auto.
Qed.

Lemma gcenv_match_eval_clock_conds:
  forall gc1 gc2 te cs v,
  eval_clock_conds gc1 te cs v ->
  locenv_match gc1 gc2 ->
  eval_clock_conds gc2 te cs v.
Proof.
  induction 1; intros.
  constructor 1; auto.
  constructor 2 with v; auto.
  eapply gcenv_match_eval_sexp; eauto.
  constructor 3 with v; auto. 
  eapply gcenv_match_eval_sexp; eauto.
Qed.

Lemma gcenv_match_eval_fbyeqs:
  forall gc1 gc2 te eh eh' l,
  eval_fbyeqs gc1 te eh eh' l ->
  locenv_match gc1 gc2 ->
  eval_fbyeqs gc2 te eh eh' l.
Proof.
  induction 1; simpl; intros.
  +constructor.
  +constructor 2 with e1; auto.
   eapply gcenv_match_eval_clock_conds; eauto.
   inv H0.
   econstructor 1; eauto.
   eapply gcenv_match_eval_sexp; eauto.
   econstructor 2; eauto.
  +constructor 3; auto.
   eapply gcenv_match_eval_clock_conds; eauto.
Qed.

Lemma gcenv_match_eval_lindexs:
  forall gc1 gc2 te t ty lis ofs o,
  eval_lindexs gc1 te t ty lis ofs o ->
  locenv_match gc1 gc2 ->
  eval_lindexs gc2 te t ty lis ofs o.
Proof.
  induction 1; simpl; intros; auto.
  constructor 1; auto.
  constructor 2 with delta ty; auto.
  constructor 3 with i; auto.
  eapply gcenv_match_eval_sexp; eauto.
Qed.

Lemma gcenv_match_eval_fbyn_init:
  forall gc1 gc2 id1 id2 aid t o i v2 e e',
  eval_fbyn_init gc1 id1 id2 aid t o i v2 e e' ->
  locenv_match gc1 gc2 ->
  eval_fbyn_init gc2 id1 id2 aid t o i v2 e e'.
Proof.
  induction 1; intros.
  constructor 1 with aty sa eh1 v'; auto.
  eapply gcenv_match_locenv_setlvar; eauto.
  constructor 2; auto.
Qed.

Lemma gcenv_match_locenv_setarys:
  forall gc1 gc2 te lhs rtys vrs te',
  locenv_setarys gc1 (Svar ACG_I type_int32s) te lhs rtys vrs te' ->
  locenv_match gc1 gc2 ->
  locenv_setarys gc2 (Svar ACG_I type_int32s) te lhs rtys vrs te'.
Proof.
  induction 1; simpl; intros.
  constructor.
  constructor 2 with e1; auto.
  eapply gcenv_match_locenv_setlvar; eauto.
Qed.

Lemma locenv_setarys_ptree_ids_none:
  forall gc1 i te lhs rtys vrs te',
  locenv_setarys gc1 i te lhs rtys vrs te' ->
  forall l, ptree_ids_none l te ->
  ptree_ids_none l te'.
Proof. 
  induction 1; intros; auto.
  apply IHlocenv_setarys; auto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
Qed.

Lemma trans_node_all_correct:
  forall gc1 e e' node1 vargs vrets,
  eval_node prog1 gc1 e e' node1 vargs vrets ->
  forall node2 gc2, trans_node (pretypeof_prog prog1) node1 = OK node2 -> 
  locenv_match gc1 gc2 ->
  pre_types_match (pretypeof_prog prog1) gc2 ->
  eval_node prog2 gc2 e e' node2 vargs vrets.
Proof.
  intros gc1.
  induction 1 using LsemS.eval_node_ind2 with 
  ( P0 := fun nk te e te' e' ss =>
      forall ss' gc2, mmap (trans_stmtclock (pretypeof_prog prog1)) ss = OK ss' ->
      locenv_match gc1 gc2 ->
      pre_types_match (pretypeof_prog prog1) gc2 ->
      ptree_ids_none (map fst (pretypeof_prog prog1)) te ->
      eval_stmts prog2 gc2 nk te e te' e' ss'
        /\ ptree_ids_none (map fst (pretypeof_prog prog1)) te')
  ( P1 := fun nk te e te' e' s cks =>
      forall s' gc2, trans_stmt (pretypeof_prog prog1) s = OK s' ->
      locenv_match gc1 gc2 ->
      pre_types_match (pretypeof_prog prog1) gc2 ->
      ptree_ids_none (map fst (pretypeof_prog prog1)) te ->
      eval_stmt prog2 gc2 nk te e te' e' s' cks
        /\ ptree_ids_none (map fst (pretypeof_prog prog1)) te')
  ( P2 := fun nk te e te' e' f =>
      forall gc2, locenv_match gc1 gc2 ->
      pre_types_match (pretypeof_prog prog1) gc2 ->
      ptree_ids_none (map fst (pretypeof_prog prog1)) te ->
      eval_hstmt prog2 gc2 nk te e te' e' f
        /\ ptree_ids_none (map fst (pretypeof_prog prog1)) te')
  ( P3 := fun nk te se se1 atys vargs i cdef rtys vrets =>
      forall gc2, locenv_match gc1 gc2 ->
      pre_types_match (pretypeof_prog prog1) gc2 ->
      ptree_ids_none (map fst (pretypeof_prog prog1)) te ->
      eval_apply prog2 gc2 nk te se se1 atys vargs i cdef rtys vrets); 
  simpl; intros.
+(*eval_node*)
  monadInv H6. 
  eapply trans_body_ids_norepet in H0; eauto.
  unfold trans_body in EQ. monadInv EQ.
  destruct (list_in_list _ _) eqn:?; try congruence. inv EQ1.
  apply exec_node with te te1 te2 eh1; simpl; auto.
  -unfold mkloopmapw, allvarsof in *; simpl. 
   erewrite <-trans_stmtclocks_has_for; eauto.
  -eapply IHeval_node; eauto.
   eapply locenv_setvars_ptree_ids_none; eauto.
   eapply alloc_variables_ptree_ids_none; eauto.
   apply list_in_list_disjoint; auto.
  -unfold eqtsof in *.
   erewrite trans_stmtclocks_fbyeqsof; eauto.
   apply trans_stmts_svars_eq in EQ0. destruct EQ0 as [A ?].
   rewrite <-A. simpl.
  eapply gcenv_match_eval_fbyeqs; eauto.
+(*eval_stmts_nil*)
  inv H. split; auto. constructor.
+(*eval_stmts_cons_true*)
  monadInv H2. monadInv EQ.
  destruct IHeval_node with x1 gc2; auto.
  destruct IHeval_node0 with x0 gc2; auto.
  split; auto.
  eapply eval_stmts_cons_true; eauto.
  eapply gcenv_match_eval_clock_conds; eauto.
+(*eval_stmts_cons_false*)
  monadInv H1. monadInv EQ.
  destruct IHeval_node with x0 gc2; auto.
  split; auto. 
  eapply eval_stmts_cons_false; eauto.
  eapply gcenv_match_eval_clock_conds; eauto.
+(*eval_Sassign*)
  inv H2. split.
  -eapply eval_Sassign; eauto.
   eapply gcenv_match_eval_expr; eauto.
   eapply gcenv_match_locenv_setlvar; eauto.
  -eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Scall*)
  inv H2. split.
  -eapply eval_Scall; eauto.
   eapply gcenv_match_eval_sexps; eauto.
  -eapply locenv_setvars_ptree_ids_none; eauto.
+(*eval_Sfor_start*)
  inv H2.
  destruct IHeval_node with (initstmtsof2 s) gc2; auto.
    destruct s; simpl; auto.
  destruct IHeval_node0 with (Sfor false s j) gc2; auto.
    eapply eval_eqf_ptree_ids_none; eauto.
  split; auto.
  apply eval_Sfor_start with te1 te2; eauto.
  eapply gcenv_match_eval_eqf; eauto.
+(*eval_Sfor_false*)
  inv H0. split; auto.
  eapply eval_Sfor_false; eauto.
  eapply gcenv_match_eval_sexp; eauto.
+(*eval_Sfor_loop*)
  inv H3.
  destruct IHeval_node with gc2; auto.
  destruct IHeval_node0 with (Sfor false s j) gc2; auto.
    eapply eval_eqf_ptree_ids_none; eauto.
  split; auto.
  apply eval_Sfor_loop with te1 te2 e1; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_eqf; eauto.
+(*eval_Sarydif_nil*)
  inv H. split; auto. 
  eapply eval_Sarydif_nil; eauto.
+(*eval_Sarydif_cons*)
  inv H4.
  destruct IHeval_node with 
    (Sarydif (lid, Tarray aid (typeof a) num) (Int.add i Int.one) al) gc2; simpl; auto.
    eapply locenv_setlvar_ptree_ids_none; eauto.
  split; auto.
  apply eval_Sarydif_cons with te1 v v'; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
+(*eval_Smix*)
  inv H4.
  destruct IHeval_node with 
    (Sassign (lid, ty) (Expr a1)) gc2; simpl; auto.
  split; auto.
  apply eval_Smix with te1 o v3 v; auto.
  eapply gcenv_match_eval_lindexs; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply store_env_ptree_ids_none; eauto.
+(*eval_Sstruct_nil*)
  inv H. split; auto. 
  eapply eval_Sstruct_nil; eauto.
+(*eval_Sstruct_cons*)
  inv H4.
  destruct IHeval_node with 
    (Sstruct (lid, ty) ftl al) gc2; simpl; auto.
    eapply locenv_setlvar_ptree_ids_none; eauto.
  split; auto.
  apply eval_Sstruct_cons with te1 v v'; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
+(*Sskip*)
  inv H. split; auto. constructor.
+(*eval_Sfby_cycle_1*)
  inv H4. split.
  apply eval_Sfby_cycle_1 with v2 v; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Sfby_cycle_n*)
  inv H4. split.
  apply eval_Sfby_cycle_n with v1 v; auto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Sfbyn_cycle_1*)
  inv H10. split.
  remember (Svar id1 _) as sa.
  remember (Tarray _ _ _) as aty.
  apply eval_Sfbyn_cycle_1 with eh1 sa aty v1 v2 v; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_fbyn_init; eauto.
  eapply gcenv_match_eval_eqf; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Sfbyn_cycle_n*)
  inv H7. split.
  remember (Svar id1 _) as sa.
  remember (Tarray _ _ _) as aty.
  apply eval_Sfbyn_cycle_n with sa aty v1 v; auto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Sarrow*)
  inv H2.
  destruct IHeval_node with (Sassign lh (Expr (if b then a1 else a2))) gc2; auto.
  split; auto.
  apply eval_Sarrow with v b; auto.
+(*eval_Scurrent_true*)
  monadInv H5. split; auto.
  apply eval_ScurrentR_true with v1 v; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Scurrent_false*)
  monadInv H2.
  destruct IHeval_node with (Sfby lh id a1 x) gc2; simpl; auto.
    rewrite EQ. auto.
  split; auto.
  apply eval_ScurrentR_false; auto.
  eapply gcenv_match_eval_sexp; eauto.
+(*eval_Spre_cycle_1*)
  monadInv H4. split.
  apply eval_Sfby_cycle_1 with v2 v; auto.
  -eapply eval_pre_genper; eauto.
   eapply pre_types_sizeof_prog1; eauto.
  -erewrite gen_pre_exp_typeof; eauto.
  -eapply gcenv_match_locenv_setlvar; eauto.
  -eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Spre_cycle_n*)
  monadInv H4. split.
  apply eval_Sfby_cycle_n with v1 v; auto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_ScurrentR_true*)
  inv H5. split.
  apply eval_ScurrentR_true with v1 v; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Scurrent_false*)
  inv H2. 
  destruct IHeval_node with (Sfby lh id a1 a2) gc2; auto.
  split; auto.
  apply eval_ScurrentR_false; auto.
  eapply gcenv_match_eval_sexp; eauto.
+(*eval_Hmaptyeq*)
  split.
  apply eval_Hmaptyeq with aid1 t b; auto.
  eapply gcenv_match_eval_typecmp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Hmapary*)
  split.
  apply eval_Hmapary with v v'; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Hmapunary*)
  split.
  apply eval_Hmapunary with t1 v v'; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Hfoldary*)
  split.
  apply eval_Hflodary; auto.
  eapply gcenv_match_eval_eqf; eauto.
  eapply eval_eqf_ptree_ids_none; eauto.
+(*eval_Hfoldunary*)
  split.
  apply eval_Hflodunary; auto.
  eapply gcenv_match_eval_eqf; eauto.
  eapply eval_eqf_ptree_ids_none; eauto.
+(*eval_Hfoldcast*)
  split.
  apply eval_Hflodcast; auto.
  eapply gcenv_match_eval_eqf; eauto.
  eapply eval_eqf_ptree_ids_none; eauto.
+(*eval_Harydef*)
  split.
  eapply eval_Harydef; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Haryslc*)
  split.
  eapply eval_Haryslc; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Hboolred_true*)
  split.
  eapply eval_Hboolred_true; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_eqf; eauto.
  eapply eval_eqf_ptree_ids_none; eauto.
+(*eval_Hboolred_false*)
  split; auto.
  eapply eval_Hboolred_false; eauto.
  eapply gcenv_match_eval_sexp; eauto.
+(*eval_Hmapcall*)
  split.
  apply eval_Hmapcall with atys rtys i vl vas vrs; auto.
  eapply gcenv_match_eval_sexps; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setarys; eauto.
  eapply locenv_setarys_ptree_ids_none; eauto.
+(*eval_Hfillcall*)
  destruct IHeval_node with (Sassign (tid, ty) (Expr (Svar lid ty))) gc2; auto.
  split. 
  apply eval_Hfillcall with te1 te2 i v vret vrs tys; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply gcenv_match_locenv_setarys; eauto.
  eapply locenv_setarys_ptree_ids_none; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Hredcall*)
  destruct IHeval_node with (Sassign (tid, ty) (Expr (Svar lid ty))) gc2; auto.
  split. 
  apply eval_Hredcall with te1 i v atys vl vargs vret; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexps; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_Hmapfoldcall*)
  destruct IHeval_node with (Sassign (tid, ty) (Expr (Svar lid ty))) gc2; auto.
  split. 
  apply eval_Hmapfoldcall with te1 te2 i v atys vl vargs vret vrs tys; auto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_eval_sexps; eauto.
  eapply gcenv_match_eval_sexp; eauto.
  eapply gcenv_match_locenv_setlvar; eauto.
  eapply gcenv_match_locenv_setarys; eauto.
  eapply locenv_setarys_ptree_ids_none; eauto.
  eapply locenv_setlvar_ptree_ids_none; eauto.
+(*eval_appay.*)
  destruct call_func_match with cdef fd as [fd' [? ?]]; auto.
  apply eval_Apply with fd' ef ef' vargs'; auto.
  -monadInv H10. unfold trans_body in EQ. monadInv EQ.
   destruct (list_in_list _ _) eqn:?; inv EQ1; auto.
  -monadInv H10. unfold trans_body in EQ. monadInv EQ; auto. 
   destruct (list_in_list _ _) eqn:?; inv EQ1; auto.
  -monadInv H10. unfold trans_body in EQ. monadInv EQ; auto.
   destruct (list_in_list _ _) eqn:?; inv EQ1; auto.
Qed.

Theorem exec_prog_correct_general:
  forall gc1 e main1 vass vrss n maxn,
  exec_prog prog1 gc1 eval_node main1 e n maxn vass vrss ->
  forall gc2 main2, trans_node (pretypeof_prog prog1) main1 = OK main2 ->
  locenv_match gc1 gc2 ->
  pre_types_match (pretypeof_prog prog1) gc2 ->
  exec_prog prog2 gc2 eval_node main2 e n maxn vass vrss.
Proof.
  induction 1; intros.
  +constructor 1 with mrss; trivial.
   monadInv H1. monadInv EQ.
   destruct (list_in_list _ _) eqn:?; inv EQ1; auto.
  +eapply trans_node_all_correct in H0; eauto.
   constructor 2 with e'; auto.
Qed.

Lemma alloc_globals_match_exists:
  forall tys gc,
  list_norepet (map fst tys) ->
  ptree_ids_none (map fst tys) gc ->
  check_pre_types (map snd tys) = true ->
  exists gc', alloc_globals gc (map gen_pre_const tys) = Some gc'
    /\ locenv_match gc gc'  
    /\ pre_types_match tys gc'.
Proof.
  induction tys; simpl; intros.
  +exists gc. split; [| split]; auto.
   red; auto. 
   red; simpl; intros. tauto.
  +rewrite Zplus_0_r.
   destruct (zlt 0 _), (zle _ _); simpl in *; try congruence. 
   rewrite Z.max_l; try omega. inv H.
   destruct store_zeros_exists with (alloc (sizeof (snd a))) (sizeof (snd a)) as [m ?]; auto.
    rewrite length_alloc. rewrite nat_of_Z_eq; try omega.
   rewrite H.
   destruct IHtys with (PTree.set (fst a) (m, snd a) gc) as [gc' [? [? ?]]]; auto.
    red; intros. rewrite PTree.gso; auto.
    apply H0. simpl; auto.
    red; intros. subst. auto.
   exists gc'. split; [| split]; auto.
   -red; intros. apply H3. rewrite PTree.gso; auto.
    red; intros. subst. rewrite H0 in H7; simpl; auto.
    congruence.
   -red. simpl; intros. 
    destruct H7; subst; simpl in *.
    *rewrite alloc_globals_notin_eq with
       (l:=map gen_pre_const tys) (gc:=PTree.set (fst (id, t)) (m, snd (id, t)) gc); auto.
     inv H8. rewrite H10 in H. inv H.
     rewrite PTree.gss; split; auto.
     erewrite store_zeros_length; eauto.
     rewrite length_alloc. rewrite nat_of_Z_eq; try omega.
     rewrite map_map. simpl. auto.
    *apply H6; auto. 
Qed.

Lemma init_node_correct:
  forall e fd,
  init_node prog1 e fd ->
  forall fd', trans_node (pretypeof_prog prog1) fd = OK fd' ->
  init_node prog2 e fd'.
Proof.
  intros until fd.
  induction 1 using init_node_ind2 with 
  ( P0 := fun e1 e2 l =>
      init_stmt prog2 e1 e2 l
   ); intros.
 +(*init_node*)
  monadInv H2.
  apply trans_body_ids_norepet with (f':=x) (tys:=pretypeof_prog prog1) in H; auto.
  unfold trans_body in EQ.
  monadInv EQ. destruct (list_in_list _ _) eqn:?; inv EQ1.
  destruct trans_stmts_svars_eq with (nd_stmt f) (pretypeof_prog prog1) x0 as [? [? ?]]; auto.
  constructor 1; simpl in *; auto.
  -rewrite <-H2, <-H3; auto.
  -rewrite <-H4; auto.  
 +(*nil*)
  constructor.
 +(*cons*)
  destruct call_func_match with c fd as [fd' [? ?]]; auto.
  constructor 2 with se1 fd' ef; auto.
  monadInv H4. monadInv EQ.
  destruct (list_in_list _ _) eqn:?; try congruence. 
  inv EQ1; auto.
Qed.

Lemma initial_states_match:
  forall gc main1 e,
  Lenv.initial_state prog1 gc init_node main1 e ->
  exists main2 gc2, Lenv.initial_state prog2 gc2 init_node main2 e
    /\ trans_node (pretypeof_prog prog1) main1 = OK main2
    /\ locenv_match gc gc2
    /\ pre_types_match (pretypeof_prog prog1) gc2.
Proof.
  induction 1; intros; try congruence.
  generalize TRANS; intros.
  monadInv TRANS. destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _ ) eqn:?; try congruence.
  destruct (names_plt _ _); try congruence.
  destruct (check_pre_types _) eqn:?; try congruence.
  destruct find_funcs_monad_exits with node node (node_block prog1) x (trans_node (pretypeof_prog prog1)) (node_main prog1) main1
     as [main2 [? ?]]; auto.
     intros. monadInv H2; auto.
  cut (fst main2 = node_main prog1). intros A.
  rewrite <-A in *.
  destruct alloc_globals_match_exists with (pretypeof_prog prog1) gc as [gc2 [? [? ?]]]; auto.
    apply check_norepeat_list_norepet; auto.
    unfold init_genvc in H. red. intros.
    rewrite alloc_globals_notin_eq with (l:=const_block prog1) (gc:=empty_locenv); auto.
    rewrite PTree.gempty; auto.
    apply list_in_list_disjoint in Heqb. red. intros. eapply Heqb; eauto.
    unfold globidsof. apply in_or_app. left. 
    apply in_or_app. auto.
  exists main2, gc2. split; [| split; [| split]]; auto.
  +constructor.
   -inv EQ0. unfold init_genvc. simpl.
    apply alloc_globals_app with gc; auto.
   -inv EQ0. simpl. auto.
   -eapply init_node_correct; eauto.
  +eapply find_funct_fid; eauto.
Qed.

Theorem trans_program_correct:
  forall gc e main1 vass vrss maxn,
  Lenv.initial_state prog1 gc init_node main1 e->
  exec_prog prog1 gc eval_node main1 e 1 maxn vass vrss ->
  exists main2 gc2, Lenv.initial_state prog2 gc2 init_node main2 e
    /\ nd_args (snd main1) = nd_args (snd main2)
    /\ nd_rets (snd main2) = nd_rets (snd main1) 
    /\ exec_prog prog2 gc2 eval_node main2 e 1 maxn vass vrss.
Proof.
  intros.
  destruct initial_states_match with gc main1 e as [main2 [gc2 [A [A1 [A2 A3]]]]]; auto.
  exists main2, gc2. repeat (split; auto).
  unfold trans_node, trans_body in A1. monadInv A1. monadInv EQ.
    destruct (list_in_list _ _) eqn:?; inv EQ1; auto.
  unfold trans_node, trans_body in A1. monadInv A1. monadInv EQ.
    destruct (list_in_list _ _) eqn:?; inv EQ1; auto.
  eapply exec_prog_correct_general; eauto.
Qed.

End CORRECTNESS.  

