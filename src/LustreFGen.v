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

(** Translation of tempo statement. *)

Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Cop.
Require Import Lop.
Require Import LustreR.
Require Import Lustre.
Require Import LustreF.
Require Import Permutation.
Require Import Inclusion.

(** Example of fbyn translation. *) 
(** x = fby(y ; 2; 10);	

typedef struct { int idx; array_int_2 items; } struct_fby;

if (outC->init) {
    for (i = 0; i < 2; i++) {
      fs.items[i] = 10;
    }
    fs.idx = 0;
  }
x = fs.items[fs.idx];
fs.items[fs.idx] = y;
fs.idx = (fs.idx + 1) % 2; *)

Definition loop_cond (j: int) :=
  Sbinop Olt (Svar ACG_J type_int32s) (Sconst (Cint j) type_int32s) type_bool.

Definition loop_init := 
  (Svar ACG_J type_int32s, Sconst (Cint Int.zero) type_int32s).

Definition loop_add :=
  (Svar ACG_J type_int32s, self_add ACG_J).

Definition cons_for(s: stmt)(i: int) :=
  Sfor (Some loop_init) (loop_cond i) loop_add s.

(** Translate fbyn. *) 

Definition cons_fbyn(lh a1 a2 sa: sexp)(i: int)(aty: type)(flag: ident): stmt :=
  let ei := Sfield sa FBYIDX type_int32s in (**r acg_fby1.idx  *) 
  let ea := Sfield sa FBYITEM aty in (**r acg_fby1.items  *) 
  let fs := Sassign (Saryacc ea (Svar ACG_J type_int32s) (typeof a2)) a2 in (**r acg_fby1.items[acg_j] = a2  *) 
  let init := Sassign ei (Sconst (Cint Int.zero) type_int32s) in (**r acg_fby1.idx = 0  *) 
  let fs := cons_for fs i in
  let s1 := Sif (Ssvar flag type_bool) (Sseq fs init) Sskip in 
  let s2 := Sassign lh (Saryacc ea ei (typeof a2)) in (**r lh = acg_fby1.items[acg_fby1.idx]  *) 
  (Sseq s1 s2).

(** Translate statement. *) 

Fixpoint trans_stmt(s: LustreR.stmt): stmt:=
  match s with
  | LustreR.Sassign lh a => Sassign lh a
  | LustreR.Scall oid lhs cdef a => Scall oid lhs cdef a
  | LustreR.Sfor a1 a2 a3 fs => Sfor a1 a2 a3 (trans_stmt fs)
  | LustreR.Sifs a s1 s2 => Sif a (trans_stmt s1) (trans_stmt s2)
  | LustreR.Scase lh a pel => Scase lh a pel
  | LustreR.Sseq s1 s2 => Sseq (trans_stmt s1) (trans_stmt s2)
  | LustreR.Sfby lh id flag a1 a2 => 
    Sif (Ssvar flag type_bool) (Sassign lh a2) (Sassign lh (Ssvar id (typeof a1)))
  | LustreR.Sfbyn lh (id1,id2,aid) flag i a1 a2 => 
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in 
     let sty := make_fbyn_type id2 aty in
     let sa := Ssvar id1 sty in
     cons_fbyn lh a1 a2 sa i aty flag
  | LustreR.Sarrow lh flag a1 a2 => Sif (Ssvar flag type_bool) (Sassign lh a1) (Sassign lh a2)
  | LustreR.Sskip => Sskip
  | LustreR.Stypecmp _ _ _ => Sskip
  end.

Fixpoint trans_expr(e: sexp): sexp :=
  match e with
  | Sconst c ty => Sconst c ty
  | Svar id ty  => Ssvar id ty
  | Scvar id ty  => Scvar id ty
  | Ssvar id ty  => Ssvar id ty
  | Savar id ty  => Savar id ty
  | Saryacc a1 a2 ty => Saryacc (trans_expr a1) (trans_expr a2) ty
  | Sfield a id ty => Sfield (trans_expr a) id ty
  | Scast a ty => Scast (trans_expr a) ty
  | Sunop op a ty => Sunop op (trans_expr a) ty
  | Sbinop op a1 a2 ty => Sbinop op (trans_expr a1) (trans_expr a2) ty
  end.

Fixpoint check_clock (conds: list sexp)(s: stmt): stmt :=
  match conds with
  | nil => s
  | cond :: rest =>
    Sif cond (check_clock rest s) Sskip
  end.

Fixpoint trans_peqs (eqs: list (eqt*list sexp)): stmt :=
  match eqs with
  | nil => Sskip
  | cons (Eqt_assign eq, conds) eql =>  
    let s := check_clock (rev conds) (Sassign (trans_expr (fst eq)) (snd eq)) in
    Sseq s (trans_peqs eql)
  | cons (Eqt_counter eq, conds) eql =>  
    let s := check_clock (rev conds) (Sassign (trans_expr (fst eq)) (trans_expr (snd eq)))  in
    Sseq s (trans_peqs eql)
  end.

(**r Translate postpositive statement of tempo statement. *) 

Fixpoint mkloopid(eqs: list (eqt*list sexp)): list (ident*type) :=
  match eqs with
  | nil => nil
  | cons (Eqt_counter eq, _) eql => (ACG_J,type_int32s)::nil
  | cons _ eql => mkloopid eql
  end.

(** Translate body of node. *)

Definition trans_body(f: LustreR.node): func :=
  let s := trans_stmt f.(nd_stmt) in  
  let s1 := trans_peqs f.(nd_eqt) in 
  let vars := mkloopid f.(nd_eqt) in
  mknode f.(nd_kind) f.(nd_args) f.(nd_rets) (nd_flags f) (nd_svars f) (nd_vars f++vars) (Sseq s s1) f.(nd_sid) f.(nd_fld) nil.

Definition trans_node(f: ident*LustreR.node): ident*func :=
  (fst f,trans_body (snd f)).

Definition trans_program (p: LustreR.program): program :=
  let nodes := map trans_node (node_block p) in
  mkprogram (type_block p) (const_block p) nodes (node_main p).

Lemma check_clock_instidof:
  forall cks s, 
  instidof (check_clock cks s) = instidof s.
Proof.
  induction cks; simpl; intros; auto. 
  rewrite <-app_nil_end; auto.
Qed.

Lemma trans_peqs_instidof:
  forall l, instidof (trans_peqs l) = nil.
Proof.
  induction l; simpl; auto.
  destruct a.
  destruct e; simpl; 
  rewrite check_clock_instidof; auto.
Qed.

Lemma trans_stmt_instidof:
  forall s, instidof (trans_stmt s) = LustreR.instidof s.
Proof.
  induction s; simpl; intros; auto.
  f_equal; auto.
  destruct p. destruct p. auto. 
  f_equal; auto.  
Qed.

Lemma mkloopid_idrange:
  forall l, mkloopid l = nil \/ mkloopid l = (ACG_J, type_int32s) :: nil.
Proof.
  induction l; simpl; auto.
  destruct a. destruct e; auto.
Qed.

Lemma mkloopid_in:
  forall l, (1 <= eqt_counter l)%nat ->
  mkloopid l = (ACG_J, type_int32s) :: nil.
Proof.
  induction l; simpl; intros; try omega.
  destruct a. destruct e; auto.
Qed.

Lemma allvarsof_permut:
  forall (f:LustreR.node) z,
  Permutation (mkloopid z ++ allvarsof f)
   (((nd_vars f ++ mkloopid z) ++ nd_args f) ++ nd_rets f).
Proof.
  intros. unfold allvarsof. 
  repeat rewrite <-app_ass. apply Permutation_app_tail.
  apply Permutation_app_tail. apply Permutation_app_swap.
Qed.

Lemma mkloopid_norepet:
  forall z, list_norepet (map fst (mkloopid z)).
Proof.
  intros.
  destruct mkloopid_idrange with z as [ | ];
  rewrite H; simpl; auto;
  constructor; auto. constructor.
Qed.

Lemma mkloopid_disjoint:
  forall (f: LustreR.node) z,
  ~ In ACG_J (allidsof f ++ LustreR.predidof f) ->
  list_disjoint (map fst (mkloopid z)) (map fst (allvarsof f)).
Proof.
  intros. destruct mkloopid_idrange with z as [ | ];
  rewrite H0; red; simpl; intros; try tauto.
  destruct H1; subst; try tauto.
  red; intros; subst. apply H; auto.
  apply in_or_app; auto.
Qed.

Lemma trans_body_allidsof_norepet:
  forall f z,
  LustreR.ids_norepet f ->
  ids_plt ACG_INIT (allidsof f ++ LustreR.predidof f) ->
  list_norepet (map fst (mkloopid z ++ allvarsof f)).
Proof.
  intros. rewrite map_app.
  apply ids_plt_le_notin with ACG_J _ _ in H0; 
   try (unfold Ple, ACG_J, ACG_INIT; omega).
  apply list_norepet_app. repeat (split; auto).
  -apply mkloopid_norepet.
  -destruct H. auto.
  -apply mkloopid_disjoint;auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f, LustreR.ids_norepet f ->
  ids_plt ACG_J (allidsof f ++ LustreR.predidof f) ->
  ids_norepet (trans_body f).
Proof.
  intros.
  assert(A: ~ In ACG_J (allidsof f ++ LustreR.predidof f)).
    apply ids_plt_le_notin with ACG_J; auto.
    unfold Ple ,ACG_J. omega.
  destruct H as [? [? ?]]. unfold trans_body.
  unfold ids_norepet, allidsof, allvarsof,LustreR.predidof,predidof in *.
  simpl in *. rewrite trans_peqs_instidof,  <-app_nil_end.
  erewrite trans_stmt_instidof; eauto.
  destruct H2.
  repeat (split; auto).
  +apply list_norepet_permut with (map fst (mkloopid (nd_eqt f) ++ allvarsof f)).
   destruct mkloopid_idrange with (nd_eqt f) as [ | ]; 
   rewrite H4; simpl; auto.
   constructor; auto.
   red. intros. apply A. apply in_or_app; auto.
   apply Permutation_map. apply allvarsof_permut.
  +apply list_disjoint_incl_left with (map fst (mkloopid (nd_eqt f)++allvarsof f)).
   destruct mkloopid_idrange with (nd_eqt f);
   rewrite H4 in *; simpl; auto.
   -red; simpl; intros. destruct H5; subst; auto.
    red; intros; subst. apply A. apply in_or_app; auto.
   -unfold allvarsof. repeat rewrite map_app. incl_tac.
Qed.

Lemma trans_program_ids_range:
  forall p, LustreR.ids_range OUTSTRUCT (node_block p) ->
  ids_range OUTSTRUCT (node_block (trans_program p)).
Proof.
  intros. simpl. red; intros. 
  apply in_map_iff with (y:=fd) in H0; auto. destruct H0 as [? [? ?]].
  subst. red in H. 
  unfold allidsof, predidof,LustreR.predidof, allvarsof in *.
  simpl in *. rewrite trans_peqs_instidof, <-app_nil_end.
  erewrite trans_stmt_instidof; eauto.
  apply H in H1; auto.
  red. intros.
  apply Permutation_in with (l':=(map fst
          (mkloopid (nd_eqt (snd x))++allvarsof (snd x)) ++ LustreR.predidof (snd x)))  in H0.
  apply in_app_or in H0. simpl in *.
  destruct H0.
  +destruct mkloopid_idrange with (nd_eqt (snd x)) as [ | ];
   rewrite H2 in *; simpl in *. 
   -apply H1. apply in_or_app; auto.
   -destruct H0; subst.
    unfold Plt, OUTSTRUCT, ACG_J. omega.
    apply H1. apply in_or_app; auto.
  +apply H1. unfold LustreR.predidof in *. in_tac.
  +unfold LustreR.predidof in *. apply Permutation_app_tail.
   apply Permutation_map. apply Permutation_sym.
   apply allvarsof_permut.
Qed.

Lemma trans_program_const_block:
  forall p,
  const_block p = const_block (trans_program p).
Proof.
  intros. auto.
Qed.

Lemma trans_program_gids_norepet:
  forall p, globidsof (trans_program p) = globidsof p.
Proof.
  intros.
  unfold globidsof. intros.
  simpl. repeat rewrite map_map. auto.
Qed.
