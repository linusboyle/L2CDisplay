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

(** Translation of type comparision. *)

Require Import Coqlib.
Require Import AST.
Require Import Integers.
Require Import Errors.
Require Import Cop.
Require Import Lident.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import LustreR.
Require Import Permutation.
Require Import ExtraList.

Local Open Scope error_monad_scope.

(** Get the name of struct or array type. *)

Definition id_of_type(t: type): res ident :=
  match t with
  | Tarray id ty num => OK id
  | Tstruct id _ => OK id
  | _ => Error (msg "TransTypecmp: not Tarray or Struct")
  end.

(** The return expr in acg_comp function. *)

Definition result := Svar ACG_EQU type_bool.

(** Then temp result expr in acg_comp function. *)

Definition local_result := Svar ACG_LOCAL type_bool.

(** The initiation statement of return expr in acg_comp function. *)

Definition result_init := Sassign result (Sconst (Cbool true) type_bool).

(** The assign statement of return expr in acg_comp function. *)

Definition result_assign := Sassign result (Sbinop Oand result local_result type_bool). (* result=result & local_result *)

(** Input parameters in acg_comp function. *)

Definition cmp_paras(ty: type) := (ACG_C1, ty) :: (ACG_C2, ty) :: nil.

(** Local variables in acg_cmp fuction of struct. *)

Definition str_vars := (ACG_LOCAL , type_bool) :: nil.

(** Local variables in acg_cmp fuction of array. *)

Definition ary_vars := (ACG_LOCAL , type_bool) :: (ACG_I , type_int32s):: nil.

(** Output parameters in acg_comp function. *)

Definition cmp_rets := (ACG_EQU,type_bool)::nil.

(** Call for type comparision function.  *)

Definition comp_cdef(id: ident)(ty: type) := 
  mkcalldef false xH (acg_comp_name id) None xH Fnil (ty::ty::nil) cmp_rets.

(** Translate statement. *)

Fixpoint trans_stmt(s: LustreR.stmt): res stmt:=
  match s with
  | LustreR.Sassign lh a => OK (Sassign lh a)
  | LustreR.Scall oid lhs cdef a => OK (Scall oid lhs cdef a)
  | LustreR.Sfor a1 a2 a3 fs =>
    do fs1 <- trans_stmt fs;
    OK (Sfor a1 a2 a3 fs1)
  | LustreR.Sifs a s1 s2 =>
    do s3 <- trans_stmt s1; 
    do s4 <- trans_stmt s2;
    OK (Sifs a s3 s4)
  | LustreR.Scase lh a pel => OK (Scase lh a pel)
  | LustreR.Sfby lh id flag a1 a2 => OK (Sfby lh id flag a1 a2)
  | LustreR.Sfbyn lh ti flag i a1 a2 => OK (Sfbyn lh ti flag i a1 a2)
  | LustreR.Sarrow lh flag a1 a2 => OK (Sarrow lh flag a1 a2)
  | LustreR.Sseq s1 s2 => 
    do s3 <- trans_stmt s1; 
    do s4 <- trans_stmt s2;
    OK (Sseq s3 s4)
  | LustreR.Stypecmp lh a1 a2 =>
    let t := typeof a1 in 
    do id <- id_of_type t; 
    OK (Scall None (lh::nil) (comp_cdef id t) (a1::a2::nil)) 
  | LustreR.Sskip => OK Sskip
  end.

Fixpoint namesof(ty: type) : list (ident*type) :=
  match ty with
  | Tarray id aty _ => (id, ty) :: namesof aty 
  | Tstruct id fld => (id, ty) :: namesof_fields fld
  | _ => nil
  end
with namesof_fields(fld: fieldlist) : list (ident*type) :=
  match fld with
  | Fnil => nil
  | Fcons id ty ftl => namesof ty ++ namesof_fields ftl
  end.

Fixpoint typesof(s: LustreR.stmt): list type:=
  match s with
  | LustreR.Stypecmp lh a1 a2 => typeof a1 :: nil
  | LustreR.Sfor _ _ _ fs => typesof fs
  | LustreR.Sifs a s1 s2 => typesof s1 ++ typesof s2
  | LustreR.Sseq s1 s2 => typesof s1 ++ typesof s2
  | _ => nil
  end.

Definition typesof_node(f: ident*LustreR.node): list type :=
  typesof (nd_stmt (snd f)).

Definition namesof_node(f: ident*LustreR.node): list (ident*type) :=
  flat_map namesof (typesof (nd_stmt (snd f))).

Definition callsof_node(f: ident*LustreR.node) : list ident :=
  map (fun it => acg_comp_name (fst it)) (namesof_node f).

(** Translate body of node. *)

Definition trans_body(b: LustreR.node): res node :=
  do s <- trans_stmt b.(nd_stmt);
  OK (mknode b.(nd_kind) b.(nd_args) b.(nd_rets) b.(nd_flags) b.(nd_svars) b.(nd_vars) s b.(nd_sid) b.(nd_fld) b.(nd_eqt)).

Definition trans_node(f: ident*LustreR.node): res (ident*node) :=
  do body <- trans_body (snd f);
  if list_in_list (callsof_node f) (allidsof (snd f)) then
    Error (msg "TransTypecmp: comp_funcs names are in global names!")
  else
    OK (fst f,body).

Definition arystr_comp_stmt(a1 a2: sexp): stmt :=
  let ele_t := typeof a1 in
  match ele_t with
  | Tarray id1 _ _ => (**r local_result = comp_array (a1, a2) *)
    Scall None (local_result::nil) (comp_cdef id1 ele_t) (a1 :: a2 :: nil)
  | Tstruct id1 _ => (**r local_result = comp_struct (a1, a2) *)
    Scall None (local_result::nil) (comp_cdef id1 ele_t) (a1 :: a2 :: nil)
  | _ => (**r local_result = a1 == a2) *) 
    Sassign local_result (Sbinop Oeq a1 a2 type_bool) 
  end.

Definition array_comp_stmt(id:ident) (ele_t: type) (num:Z) : stmt :=
  let ty := Tarray id ele_t num in
  let para1 := Svar ACG_C1 ty in
  let para2 := Svar ACG_C2 ty in
  let i := Svar ACG_I type_int32s in
  let num := Int.repr num in
  let fs := arystr_comp_stmt (Saryacc para1 i ele_t) (Saryacc para2 i ele_t) in
  Sfor None (loop_cond num) loop_add (Sseq fs result_assign).

(** Make the body of array comparision function. *)

Definition array_comp_body(id:ident)(ele_t: type) (num:Z) : node  :=
  let ty := Tarray id ele_t num in
  let para1 := Svar ACG_C1 ty in
  let para2 := Svar ACG_C2 ty in
  let i := Svar ACG_I type_int32s in
  let num := Int.repr num in
  let fs := arystr_comp_stmt (Saryacc para1 i ele_t) (Saryacc para2 i ele_t) in
  let comp_s :=  Sfor (Some loop_init) (loop_cond num) loop_add (Sseq fs result_assign) in     
  let ss := (Sseq result_init comp_s) in
  (mknode false (cmp_paras ty) cmp_rets nil nil ary_vars ss xH Fnil nil) .

Fixpoint struct_comp_stmt_rec(para1 para2: sexp)(fl : fieldlist): stmt := 
  let ty := typeof para1 in 
  match fl with
  | Fnil => Sskip
  | Fcons label ele_t flt =>
    let s1 :=  arystr_comp_stmt (Sfield para1 label ele_t) (Sfield para2 label ele_t) in
    let comp_s1 := Sseq s1 result_assign in  
    Sseq comp_s1 (struct_comp_stmt_rec para1 para2 flt)
  end.

Definition struct_comp_stmt (id:ident) (fl: fieldlist) : stmt :=
  let ty := Tstruct id fl in    
  let para1 := Svar ACG_C1 ty in
  let para2 := Svar ACG_C2 ty in
  struct_comp_stmt_rec para1 para2 fl.

(** Make the body of struct comparision function. *) 

Definition struct_comp_body (id:ident) (fl: fieldlist) : node :=
  let ty := Tstruct id fl in    
  let comp_s := struct_comp_stmt id fl in       
  let ss := (Sseq result_init comp_s) in
  (mknode false (cmp_paras ty) cmp_rets nil nil str_vars ss xH Fnil nil).

(** Make array comparision function. *)   

Definition array_comp(id:ident)(ele_t: type) (num:Z) : ident*node  :=
  (acg_comp_name id, array_comp_body id ele_t num).

(** Make struct comparision function.  *)   

Definition struct_comp (id:ident) (fl: fieldlist) : ident*node :=
  (acg_comp_name id, struct_comp_body id fl).

(** Make list of comparision function. *)

Fixpoint comp_functions (types: list (ident*type)): list (ident * node) := 
  match types with
  | nil => nil
  | (lty_id, lty) :: rest => 
    let comp_functions_tl := comp_functions rest in
    match lty with
    | Tarray _ ele_t num =>
      let array_comp := array_comp lty_id ele_t num in    
      (array_comp::comp_functions_tl)
    | Tstruct _ fl => 
      let struct_comp := struct_comp lty_id fl in
      (struct_comp::comp_functions_tl)
    | _  => comp_functions_tl      
    end
  end.


Definition filter_type_block(l: list ident)(tbl: list (ident*type)) :=
  filter (fun x => in_list (fst x) l) tbl.

Fixpoint check_type_block(tcs tbl: list (ident*type)) : bool :=
  match tcs with
  | nil => true
  | (id, ty) :: tl =>
    match find_funct tbl id with
    | None => false
    | Some (_, ty1) => type_compare ty ty1 && check_type_block tl tbl
    end
  end.

(** Translate program. *)   

Definition make_comp_types(p: LustreR.program): res (list (ident*type)) :=
  let names := flat_map namesof_node (node_block p) in
  let tbl := filter_type_block (map fst names) (type_block p) in
  if check_type_block names tbl then
    OK tbl
  else
    Error (msg "TransTypecmp: comp_funcs types are not in global types !").

Definition trans_program(p: LustreR.program): res program :=
  do nodes <- mmap trans_node (node_block p); 
  do tbl <- make_comp_types p;
  let comp_funcs := comp_functions tbl in
  if list_in_list (map fst comp_funcs) (globidsof p) then
    Error (msg "TransTypecmp: comp_funcs names are in global names!")
  else
    if check_norepeat (map fst comp_funcs) then
      if names_plt ACG_EQU (map fst comp_funcs) then
        OK (mkprogram (type_block p) (const_block p) (comp_funcs ++ nodes) (node_main p))
      else
        Error (msg "TransTypecmp: comp_funcs names are in local temp names!")
    else Error (msg "TransTypecmp: acg_comp_function names are repeated!").

Lemma field_type_namesof_field:
  forall fld id ty a,
  field_type id fld = OK ty ->
  In a (namesof ty) ->
  In a (namesof_fields fld).
Proof.
  induction fld; simpl; intros; try congruence.
  compare id i; intros. 
  subst. rewrite peq_true in *. inv H.
  apply in_or_app. auto.
  rewrite peq_false in *; auto.
  apply in_or_app. right.
  eapply IHfld; eauto.
Qed.

Lemma trans_stmt_instidof_eq:
  forall s s',
  trans_stmt s = OK s' ->
  instidof s' = LustreR.instidof s.
Proof.
  induction s; intros; inv H; auto.
  +monadInv H1. simpl; auto. 
  +monadInv H1. simpl; f_equal; auto.
  +monadInv H1. simpl. f_equal; auto.
  +monadInv H1. simpl. auto.
Qed.

Lemma trans_stmt_fbysvarsof:
  forall s s',
  trans_stmt s = OK s' ->
  fbyvarsof s' = LustreR.fbyvarsof s.
Proof.
  induction s; simpl; intros; inv H; auto.
  +monadInv H1. simpl. eauto.
  +monadInv H1. simpl. f_equal; eauto.
  +monadInv H1. simpl. f_equal; eauto.
  +monadInv H1. simpl. auto.
Qed.

Lemma trans_body_ids_norepet:
  forall f f',
  LustreR.ids_norepet f ->
  trans_body f = OK f' ->
  ids_norepet f'.
Proof.
  unfold ids_norepet, LustreR.ids_norepet, allidsof, allvarsof, predidof,
  LustreR.predidof. intros. 
  monadInv H0. simpl in *.
  erewrite trans_stmt_instidof_eq; eauto.
Qed.

Lemma arystr_comp_stmt_fbyvarsof:
  forall a1 a2,
  fbyvarsof (arystr_comp_stmt a1 a2) = nil.
Proof.
  unfold arystr_comp_stmt. intros.
  destruct (typeof a1); auto.
Qed.

Lemma arystr_comp_stmt_instidof:
  forall a1 a2,
  instidof (arystr_comp_stmt a1 a2) = nil.
Proof.
  unfold arystr_comp_stmt. intros.
  destruct (typeof a1); auto.
Qed.

Lemma array_cmp_vars_norepet:
  list_norepet (ACG_LOCAL :: ACG_I :: ACG_C1 :: ACG_C2 :: ACG_EQU :: nil).
Proof.
  unfold ACG_LOCAL, ACG_I, ACG_C1, ACG_C2, ACG_EQU.
  repeat (split; auto). constructor; auto.
  red; simpl; intros.
  destruct H as [ | [ | [ | [ | ]]]]; congruence.
  constructor; auto.
  red; simpl; intros.
  destruct H as [ | [ | [ | ]]]; congruence.
  constructor; auto.
  red; simpl; intros. destruct H as [ | [ | ]]; congruence.
  constructor; auto. red; simpl; intros. destruct H; congruence.
  constructor; auto. constructor.
Qed.  

Lemma array_comp_body_ids_norepet:
  forall aid aty num,
  ids_norepet (array_comp_body aid aty num).
Proof.
  unfold ids_norepet, LustreR.ids_norepet, allidsof, allvarsof, predidof,
  LustreR.predidof. intros. simpl.
  rewrite arystr_comp_stmt_instidof; auto.
  repeat (split; auto).
  +apply array_cmp_vars_norepet.
  +simpl; constructor.
  +red; simpl; intros; tauto.
  +simpl. unfold ACG_LOCAL, ACG_I, ACG_C1, ACG_C2, ACG_EQU.
   red; intros. destruct H as [ | [ | [ | ]]]; congruence.
Qed.

Lemma struct_comp_stmt_fbyvarsof:
  forall fld a1 a2,
  fbyvarsof (struct_comp_stmt_rec a1 a2 fld) = nil.
Proof.
  induction fld; simpl; intros; auto.
  rewrite arystr_comp_stmt_fbyvarsof; auto.
  rewrite IHfld; auto.
Qed.

Lemma struct_comp_stmt_instidof:
  forall fld a1 a2,
  instidof (struct_comp_stmt_rec a1 a2 fld) = nil.
Proof.
  induction fld; simpl; intros; auto.
  rewrite arystr_comp_stmt_instidof; auto.
  rewrite IHfld; auto.
Qed.

Lemma struct_cmp_vars_norepet:
  list_norepet (ACG_LOCAL :: ACG_C1 :: ACG_C2 :: ACG_EQU :: nil).
Proof.
  unfold ACG_LOCAL, ACG_C1, ACG_C2, ACG_EQU.
  repeat (split; auto).
  +constructor; auto.
   red; simpl; intros.
   destruct H as [ | [ | [ | ]]]; congruence.
   constructor; auto.
   red; simpl; intros.
   destruct H as [ | [ | ]]; congruence.
   constructor; auto.
   red; simpl; intros. destruct H as [ | ]; congruence.
   constructor; auto. constructor.
Qed.

Lemma struct_comp_body_ids_norepet:
  forall sid fld,
  ids_norepet (struct_comp_body sid fld).
Proof.
  unfold ids_norepet, LustreR.ids_norepet, allidsof, allvarsof, predidof,
  LustreR.predidof. intros. simpl.
  unfold struct_comp_stmt.
  rewrite struct_comp_stmt_instidof; auto. simpl.
  repeat (split; auto).
  +apply struct_cmp_vars_norepet.
  +constructor.
  +red; simpl; intros; tauto.
  +unfold ACG_LOCAL, ACG_C1, ACG_C2, ACG_EQU, ACG_I.
   red; intros. destruct H as [ | [ | [ | ]]]; congruence.
Qed.

Lemma trans_body_ids_plt:
  forall f f' id, ids_plt id (allidsof f ++ LustreR.predidof f) ->
  trans_body f = OK f' ->
  ids_plt id (allidsof f' ++ predidof f').
Proof.
  unfold allidsof,predidof,allvarsof, LustreR.predidof.
  intros. monadInv H0. simpl in *.
  erewrite trans_stmt_instidof_eq; eauto.
Qed.

Lemma comp_functions_ids_plt:
  forall fd l, 
  In fd (comp_functions l) ->
  ids_plt ACG_J (allidsof (snd fd) ++ predidof (snd fd)).
Proof.
  induction l; simpl; intros; try tauto.
  destruct a. 
  destruct t; simpl in *; auto;
  destruct H; subst; auto; simpl.
  +unfold array_comp_body. unfold predidof. simpl.
   rewrite arystr_comp_stmt_instidof.
   simpl. unfold ACG_J, ACG_LOCAL, ACG_I, ACG_C1, ACG_C2, ACG_EQU.
   red; simpl; intros. unfold Plt.
   destruct H as [ | [ | [ | [ | [|]]]]]; subst; try omega.
  +unfold struct_comp_body. unfold predidof. simpl.
   unfold struct_comp_stmt.
   rewrite struct_comp_stmt_instidof.
   simpl. unfold ACG_J, ACG_LOCAL, ACG_C1, ACG_C2, ACG_EQU.
   red; simpl; intros. unfold Plt.
   destruct H as [ | [ | [ | [ | ]]]]; subst; try omega. 
Qed.

Lemma filter_type_block_incl:
  forall l names,
  incl (filter_type_block names l) l.
Proof.
  induction l; simpl; intros; red; intros; auto.
  destruct (in_list _ _); simpl in *.
  destruct H; [left | right]; auto.
  apply IHl in H; auto.
  right. apply IHl in H; auto.
Qed.

Lemma comp_functions_app:
  forall l1 l2,
  comp_functions (l1 ++ l2) = comp_functions l1 ++ comp_functions l2.
Proof.
  induction l1; simpl; intros; auto.
  destruct a. destruct t; auto; rewrite IHl1; auto.
Qed.

Lemma filter_type_block_norepet:
  forall l names,
  list_norepet (map fst l) ->
  list_norepet (map fst (filter_type_block names l)).
Proof.
  induction l; simpl; intros.
  constructor.
  inv H. destruct (in_list _ _); simpl; auto.
  constructor; auto.
  red. intros. apply H2. eapply map_incl; eauto.
  apply filter_type_block_incl; auto.
Qed.

Lemma trans_program_ids_range:
  forall p p', LustreR.ids_range ACG_J (node_block p) ->
  trans_program p = OK p' ->
  ids_range ACG_J (node_block p').
Proof.
  unfold LustreR.ids_range, ids_range. intros.
  monadInv H0. destruct (list_in_list _ _) eqn:?; try congruence.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _); inv EQ2.
  apply list_in_list_disjoint in Heqb.
  unfold make_comp_types in EQ1.
  destruct (check_type_block _ _) eqn:?; inv EQ1.
  simpl in *.
  apply in_app_or in H1. destruct H1.
  +apply comp_functions_ids_plt with (filter_type_block (map fst (flat_map namesof_node (node_block p)))
             (type_block p)); auto.
  +generalize H0; intros. 
   eapply in_mmap_iff in H1; eauto.
   destruct H1 as [fd1 [? ?]].
   apply H in H2.
   monadInv H1. destruct (list_in_list _ _) eqn:?; inv EQ1.
   simpl in *. eapply trans_body_ids_plt; eauto.
Qed.

Lemma trans_program_gids_norepet:
  forall p p',
  trans_program p = OK p' ->
  list_norepet (globidsof p) ->
  list_norepet (globidsof p').
Proof.
  unfold trans_program, globidsof. intros.
  monadInv H. destruct (list_in_list _ _) eqn:?; try congruence.
  apply list_in_list_disjoint in Heqb; auto.
  destruct (check_norepeat _) eqn:?; try congruence.
  destruct (names_plt _ _); inv EQ2.
  unfold make_comp_types in EQ1.
  destruct (check_type_block _ _) eqn:?; inv EQ1.
  simpl in *. apply trans_nodes_fids_eq in EQ.
  apply list_norepet_permut with 
        (map fst (comp_functions (filter_type_block (map fst (flat_map namesof_node (node_block p))) (type_block p))) 
        ++ (map fst (type_block p) ++ map fst (const_block p)) ++ map fst (node_block p)); auto.
  +apply list_norepet_app; auto. repeat (split; auto).
   apply check_norepeat_list_norepet; auto.
  +repeat rewrite map_app. rewrite <-EQ.
   repeat rewrite <-app_ass. apply Permutation_app_tail.
   apply Permutation_trans with 
        (map fst (comp_functions (filter_type_block (map fst (flat_map namesof_node (node_block p))) (type_block p)))
         ++ (((map fst (type_block p)) ++ map fst (const_block p)))); auto.
   -repeat rewrite app_ass. apply Permutation_refl. 
   -apply Permutation_app_swap. 
  +intros. monadInv H.
   destruct (list_in_list _ _) eqn:?; inv EQ1. auto.
Qed.
