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
Require Import Integers.
Require Import Inclusion.
Require Import Cop.
Require Import Ctypes.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import Permutation.
Require Import ExtraList.

Inductive hstmt: Type:=
  | Hmapary: ident*type -> binary_operationL -> sexp -> sexp -> hstmt
  | Hmaptycmp: ident*type -> bool -> sexp -> sexp -> hstmt 
  | Hmapunary: ident*type -> unary_operationL -> sexp -> hstmt
  | Hfoldary: ident*type -> binary_operationL -> sexp -> sexp -> hstmt
  | Hfoldunary: ident*type -> unary_operation -> sexp -> hstmt
  | Hfoldcast: ident*type -> sexp -> type -> hstmt
  | Harydef: ident*type -> sexp -> hstmt 
  | Haryslc: ident*type -> sexp -> int -> hstmt 
  | Hboolred: ident*type -> sexp -> hstmt
  | Hmapcall: lhs -> calldef -> list sexp -> hstmt
  | Hfillcall: ident*type -> ident*type -> lhs -> calldef -> sexp -> hstmt
  | Hredcall: ident*type -> ident*type -> calldef -> sexp -> list sexp -> hstmt
  | Hmapfoldcall: ident*type -> ident*type -> lhs -> calldef -> sexp -> list sexp -> hstmt.
  
Inductive expr: Type:=
  | Expr: sexp -> expr 
  | Earyprj: sexp -> list sexp -> sexp -> expr 
  | Ecase: sexp -> list (patn*sexp) -> expr
  | Eif: sexp -> sexp -> sexp -> expr
  | Eprefix: binary_operationL -> list sexp -> expr
  | Etypecmp: bool -> sexp -> sexp -> expr
  | Emerge: sexp -> list (patn*sexp) -> expr.

Inductive stmt: Type :=
  | Sassign: ident*type -> expr -> stmt
  | Scall: lhs -> calldef -> list sexp -> stmt
  | Sfor: bool -> hstmt -> int -> stmt
  | Sarydif: ident*type -> int -> list sexp -> stmt
  | Smix: ident*type ->sexp -> list lindex -> sexp ->  stmt
  | Sstruct: ident*type -> fieldlist -> list sexp -> stmt
  | Sfby: ident*type -> ident -> sexp -> sexp -> stmt
  | Sfbyn: ident*type -> (ident*ident*ident) -> int -> sexp -> sexp -> stmt 
  | Sarrow: ident*type -> sexp -> sexp -> stmt  
  | Scurrent: ident*type -> ident -> sexp -> sexp -> stmt
  | Spre : ident*type -> ident -> sexp -> stmt
  | ScurrentR: ident*type -> ident -> sexp -> sexp -> sexp -> stmt
  | Sskip: stmt.

Definition ridl_of_e (e: expr) : list ident :=
  match e with
  | Expr a => get_expids a
  | Earyprj a1 al a2 => get_expids a1 ++ get_expsids al ++ get_expids a2
  | Ecase a pl => get_expids a ++ flat_map (fun p => get_expids (snd p)) pl
  | Eif a1 a2 a3 => get_expids a1 ++ get_expids a2 ++ get_expids a3
  | Eprefix _ al => get_expsids al
  | Etypecmp _ a1 a2 => get_expids a1 ++ get_expids a2
  | Emerge a pl => get_expids a ++ flat_map (fun p => get_expids (snd p)) pl
  end.

Definition lidl_of_fs (fs: hstmt): list ident :=
  match fs with
  | Hmaptycmp a _ _  _ => fst a :: nil
  | Hmapary a _ _ _ => fst a :: nil
  | Hmapunary a _ _ => fst a :: nil
  | Hfoldary a _ _ _  => fst a :: nil
  | Hfoldunary a _ _  => fst a :: nil
  | Hfoldcast a _ _  => fst a :: nil
  | Harydef a _ => fst a :: nil
  | Haryslc a _ _ => fst a :: nil
  | Hboolred a _ => fst a :: nil
  | Hmapcall lh _ _ => map fst lh
  | Hfillcall a f lh _ _  => fst a :: fst f :: map fst lh
  | Hredcall a f _ _ _  => fst a :: fst f :: nil
  | Hmapfoldcall a f lh _ _ _  => fst a :: fst f :: map fst lh
  end.

Definition lidl_of_s (s: stmt) : list ident :=
  match s with
  | Sassign a  _ => fst a :: nil
  | Scall lh _ _ => map fst lh
  | Sfor _ fs _ => lidl_of_fs fs
  | Sarydif a _ _  => fst a :: nil
  | Smix a _ _ _ => fst a :: nil
  | Sstruct a _ _ => fst a :: nil
  | Sfbyn a _ _ _ _ => fst a :: nil
  | Sfby a _ _ _ => fst a :: nil
  | Sarrow a _ _ => fst a :: nil 
  | Scurrent a _ _ _ => fst a :: nil
  | Spre a _ _ => fst a :: nil
  | ScurrentR a _ _ _ _ => fst a :: nil
  | Sskip => nil
  end. 

Definition ridl_of_fs (fs: hstmt): list ident :=
  match fs with
  | Hmaptycmp _ _ e1 e2 => get_expids e1 ++ get_expids e2 
  | Hmapary _ _ e1 e2 => get_expids e1 ++ get_expids e2 
  | Hmapunary _ _ e1 => get_expids e1 
  | Hfoldary _ _ e1 e2  => get_expids e1 ++ get_expids e2
  | Hfoldunary _ _ e1 => get_expids e1
  | Hfoldcast _ e1 _ => get_expids e1
  | Harydef _ e => get_expids e
  | Haryslc _ e _ => get_expids e
  | Hboolred _ e => get_expids e
  | Hmapcall _ _ el => get_expsids el
  | Hfillcall _ _ _ _ e => get_expids e
  | Hredcall _ _ _ e el => get_expids e ++ get_expsids el
  | Hmapfoldcall _ _ _ _ e el => get_expids e ++ get_expsids el
 end.

Definition ridl_of_s (s: stmt) : list ident :=
  match s with
  | Sassign _ e => ridl_of_e e
  | Scall _ _ el => get_expsids el
  | Sfor _ fs _ => ridl_of_fs fs                
  | Sarydif _ _ el => get_expsids el           
  | Smix _ e1 lil e2 => get_expids e1 ++ get_lindexids lil ++ get_expids e2
  | Sstruct _ _ cs => get_expsids cs
  | Sfbyn _ _ _ _ a2 =>  get_expids a2
  | Sfby _ _ _ a2 =>  get_expids a2
  | Sarrow _ a1 a2 => get_expids a1 ++ get_expids a2
  | Scurrent _ _ a a1 => get_expids a ++ get_expids a1
  | Spre _ _ _ => nil
  | ScurrentR _ _ a a1 a2 => get_expids a ++ get_expids a1 ++ get_expids a2 
  | Sskip => nil
  end.

Definition ridl_of_sc (s: stmt*clock) : list ident :=
  map snd(snd s) ++ ridl_of_s (fst s).

Definition deps_of_stmt (ss: list (stmt*clock))(n: nat): depend :=
  let s := nth n ss (Sskip,nil) in 
  mkdepend (lidl_of_s (fst s)) (ridl_of_sc s) n.

Definition deps_of_stmts (ss: list (stmt*clock)): list depend :=
  map (deps_of_stmt ss) (seq O (length ss)).

Definition deps_of_stmts_simpl (eqs: list (stmt*clock)) : list depend :=
  map (fun eq =>  mkdepend (lidl_of_s (fst eq)) (ridl_of_sc eq) O) eqs.

Definition has_for(s: stmt): Z :=
  match s with
  | Sfor _ hs _ => 1
  | _ => 0
  end.

Fixpoint has_fors(l: list (stmt*clock)): Z :=
  match l with
  | nil => 0
  | cons (s, c) sl => 
     let z := has_for s in
     if zlt z 1 then Zmax z (has_fors sl) else 1 
  end.

Definition mkloopmapw(l: list (stmt*clock)): params :=
  match has_fors l with
  | 0 => nil
  | _ => (ACG_I,type_int32s) :: nil
  end.

Definition trans_prefix_unary_expr (op: unary_operationL)(val: sexp)(ty: type) : sexp :=
  match op with
  | Obool => Scast val (Cltypes.Tint IBool Signed)
  | Ochar => Scast val (Cltypes.Tint I8 Signed)
  | Oshort => Scast val (Cltypes.Tint I16 Signed)
  | Oint => Scast val (Cltypes.Tint I32 Signed)
  | Ofloat => Scast val (Cltypes.Tfloat F32)
  | Oreal => Scast val (Cltypes.Tfloat F64)
  | Onot => Sunop Cop.Onotbool val ty
  | Opos => val
  | Oneg => Sunop Cop.Oneg val ty
  end.

Definition prefix_unary_type (op: unary_operationL)(aty ty: type): Prop :=
  match op with
  | Obool => ty = Tint IBool Signed
  | Ochar => ty = Tint I8 Signed
  | Oshort => ty = Tint I16 Signed
  | Oint => ty = Tint I32 Signed
  | Ofloat => ty = Tfloat F32
  | Oreal => ty = Tfloat F64
  | Onot => True
  | Opos => ty = aty
  | Oneg => True
  end.

Definition lids_of_e (e: expr) : list ident :=
  match e with
  | Expr a => get_lids a
  | Earyprj a1 al a2 => get_lids a1 ++ get_lids a2
  | Ecase a pl => flat_map (fun p => get_lids (snd p)) pl
  | Eif a1 a2 a3 => get_lids a2 ++ get_lids a3
  | Eprefix _ al => nil
  | Etypecmp _ a1 a2 => get_lids a1 ++ get_lids a2
  | Emerge a pl => flat_map (fun p => get_lids (snd p)) pl
  end.

Definition clockof(s: stmt*clock) : list clock :=
  match fst s with
  | Sfby _ _ _ _ | Sfbyn _ _ _ _ _ | Sarrow _ _ _ | Scurrent _ _ _ _ | Spre _ _ _ | ScurrentR _ _ _ _ _ => snd s :: nil
  | _ => nil
  end.

Definition clocksof(ss: list (stmt*clock)) : list clock :=
  flat_map clockof ss.

Fixpoint gclockvarsof_rec(l: list clock) : list ((ident*type)*clock) :=
  match l with
  | nil => nil
  | cks :: tl =>
      match cks with
      | nil => ((ACG_INIT, type_bool), nil) ::nil
      | _ => gclockvarsof_rec tl
      end
  end.

Fixpoint clockvarsof_rec(l: list clock)(flags : list ((ident*type)*clock)) :=
  match l with
  | nil => flags
  | cks :: tl =>
      let flags1 := clockvars cks flags in
      clockvarsof_rec tl flags1
  end.

Definition clockvarsof(l: list clock) :=
  gclockvarsof_rec l ++ clockvarsof_rec l nil.

Definition fbyvarsof_s(s: stmt): params:=
  match s with
  | Sfby lh id a1 a2 => (id,typeof a1)::nil
  | Sfbyn lh (id1,id2,aid) i a1 a2 => 
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in 
     (id1,make_fbyn_type id2 aty)::nil
  | Scurrent lh id a a1 => (id,typeof a1)::nil
  | Spre lh id a1 => (id,typeof a1)::nil
  | ScurrentR lh id a a1 a2 => (id,typeof a1)::nil
  | _ => nil
  end.

Definition fbyeqof(sc: stmt*clock): list (eqt*list sexp) :=
  let c := clock_conds (snd sc) in
  match (fst sc) with
  | Sfby lh id a1 a2 => (Eqt_assign (Svar id (typeof a1), a1), c)::nil
  | Sfbyn lh (id1,id2,aid) i a1 a2 => 
     let aty := Tarray aid (typeof a1) (Int.unsigned i) in 
     let sty := make_fbyn_type id2 aty in
     let sa := Svar id1 sty in
     let eq1 := (Eqt_assign (Saryacc (Sfield sa FBYITEM aty) (Sfield sa FBYIDX type_int32s) (typeof a1), a1), c) in
     let eq2 := (Eqt_counter (index_incr sa i), c) in
     eq1 :: eq2 :: nil
  | Scurrent lh id a a1 => (Eqt_assign (Svar id (typeof a1), a1), c)::nil
  | Spre lh id a1 => (Eqt_assign (Svar id (typeof a1), a1), c)::nil
  | ScurrentR lh id a a1 a2 => (Eqt_assign (Svar id (typeof a1), a1), c)::nil
  | _ => nil
  end.

Definition fbyvarsof(ss: list (stmt*clock)): params :=
  flat_map (fun s => fbyvarsof_s (fst s)) ss.

Definition fbyeqsof(ss: list (stmt*clock)): list (eqt*list sexp) :=
  flat_map fbyeqof ss.

Definition eqtsof(ss: list (stmt*clock)): list (eqt*list sexp) :=
  fbyeqsof ss ++ clockresetsof (clockvarsof (clocksof ss)).
 
Definition instidofh(h: hstmt): list calldef :=
  match h with 
  | Hmapcall _ c _ => cons_inst c
  | Hfillcall _ _ _ c _  => cons_inst c
  | Hredcall _ _ c _ _  => cons_inst c
  | Hmapfoldcall _ _ _ c _ _  => cons_inst c
  | _ => nil
  end.

Definition instidof_s(s: stmt): list calldef :=
  match s with 
  | Scall _ c _ => cons_inst c
  | Sfor _ h _ => instidofh h
  | _ => nil
  end.

Definition instidof(ss: list (stmt*clock)): list calldef :=
  flat_map (fun s => instidof_s (fst s)) ss.

Definition initstmtsof1(f: hstmt): list (stmt*clock) :=
  match f with
  | Hfoldary lh _ init _ => (Sassign lh (Expr init),nil) :: nil
  | Hfoldunary lh _ init => (Sassign lh (Expr init),nil) :: nil
  | Hfoldcast lh init _ => (Sassign lh (Expr init),nil) :: nil
  | Hboolred lh _ => (Sassign lh (Expr (Sconst (Cint Int.zero) type_int32s)),nil) :: nil
  | Hfillcall lh _ _ _ init => (Sassign lh (Expr init),nil) :: nil
  | Hredcall lh _ _ init _ => (Sassign lh (Expr init),nil) :: nil
  | Hmapfoldcall lh _ _ _ init _ => (Sassign lh (Expr init),nil) :: nil
  | _ => nil 
  end.

Definition initstmtsof2(f: hstmt): list (stmt*clock) :=
  match f with
  | Hfoldary lh _ init _ => (Sassign lh (Expr init),nil) :: nil
  | Hfoldunary lh _ init => (Sassign lh (Expr init),nil) :: nil
  | Hfoldcast lh init _ => (Sassign lh (Expr init),nil) :: nil
  | Hboolred lh _ => (Sassign lh (Expr (Sconst (Cint Int.zero) type_int32s)),nil) :: nil
  | Hfillcall lh _ _ _ init => (Sassign lh (Expr init),nil) :: nil
  | Hredcall lh _ _ init _ => (Sassign lh (Expr init),nil) :: nil
  | Hmapfoldcall lh _ _ _ init _ => (Sassign lh (Expr init),nil) :: nil
  | _ => nil 
  end.

Definition nodenil:= (xH,mknode true nil nil nil nil nil (@nil (stmt*clock)) xH Fnil nil).

Definition node: Type := general_node (list (stmt*clock)).

Definition predidof(f: node) :=
  map fst (map fst (clockvarsof (clocksof (nd_stmt f))) ++ fbyvarsof (nd_stmt f)) ++ map instid (instidof (nd_stmt f)).

Definition ids_norepet(f: node) :=
  list_norepet (allidsof f) /\ list_norepet (predidof f) 
   /\ list_disjoint (allidsof f) (predidof f).

Definition program: Type := general_program node.

Definition nodup_lids (l: list depend) := 
  list_norepet (flat_map (fun a => lidl a) l). 

Definition ids_range(id: ident)(l: list (ident*node)): Prop :=
  forall fd, In fd l ->
  ids_plt id (allidsof (snd fd) ++ predidof (snd fd)).

Definition clocks_determ(l: list clock) : Prop :=
  forall c1 c2, In c1 l -> In c2 l -> 
  flagid c1 = flagid c2 -> c1 = c2.

Lemma gclockvarsof_rec_eq:
  forall ss,
  gclockvarsof_rec ss = nil \/ gclockvarsof_rec ss = ((ACG_INIT, type_bool),nil) :: nil.
Proof.
  induction ss; simpl; intros; auto.
  destruct a; auto. 
Qed.

Lemma gclockvarsof_rec_cons_eq:
  forall c cs,
  exists l, gclockvarsof_rec (c :: cs) = l ++ gclockvarsof_rec cs.
Proof.
  intros. simpl.
  destruct gclockvarsof_rec_eq with cs; rewrite H.
  +destruct c.
   exists ((ACG_INIT, type_bool, nil) :: nil); auto.
   exists nil; auto.
  +destruct c; exists nil; auto.
Qed.

Lemma clockvars_swap_permut_map:
  forall c1 c2 l,
  Permutation (map fst (clockvars c1 (clockvars c2 l))) (map fst (clockvars c2 (clockvars c1 l))).
Proof.
  destruct c1, c2; simpl; intros; auto.
  destruct p. destruct p0.
  destruct (in_list (flagidof b0 i0) (map fst (map fst l))) eqn:?; auto. 
  +destruct (in_list (flagidof b i) (map fst (map fst l))) eqn:?; auto.
   rewrite Heqb1. auto.
   rewrite map_app, map_app, in_list_app.
   simpl. rewrite Heqb1. simpl. rewrite map_app; auto.
  +rewrite map_app, map_app, in_list_app.
   destruct (in_list (flagidof b i) (map fst (map fst l))) eqn:?; simpl; auto.
   -rewrite Heqb1. auto.
   -simpl. rewrite map_app, map_app, in_list_app.
    rewrite Heqb1. simpl.
    cut (identeq (flagidof b0 i0) (flagidof b i) = identeq (flagidof b i) (flagidof b0 i0)). intros.
    rewrite H.
    destruct (identeq (flagidof b i) (flagidof b0 i0)) eqn:?; simpl; auto.
    *apply Pos.eqb_eq in H. rewrite H.
     repeat rewrite map_app; simpl. auto.
    *repeat rewrite app_ass. simpl. apply Permutation_map.
     apply Permutation_app; auto.
     constructor 3; auto.
    *rewrite Pos.eqb_sym; auto.
Qed.

Lemma clockvars_permut_map:
  forall c l1 l2,
  Permutation (map fst l1) (map fst l2) ->
  Permutation (map fst (clockvars c l1)) (map fst (clockvars c l2)).
Proof.
  destruct c; simpl; intros; auto.
  destruct p. rewrite in_list_perm with (l2:=map fst (map fst l2)).
  destruct (in_list (flagidof b i) (map fst (map fst l2))) eqn:?; auto.
  rewrite map_app, map_app. apply Permutation_app; auto.
  apply Permutation_map; auto.
Qed.

Lemma clockvarsof_rec_permut_map1:
  forall l l1 l2,
  Permutation (map fst l1) (map fst l2) ->
  Permutation (map fst (clockvarsof_rec l l1)) (map fst (clockvarsof_rec l l2)).
Proof.
  induction l; simpl; intros; auto.
  destruct a; auto.
  eapply IHl; auto.
  eapply clockvars_permut_map; eauto.
Qed.

Lemma gclockvarsof_rec_permut:
  forall s1 s2,
  Permutation s1 s2 ->
  Permutation (gclockvarsof_rec s1) (gclockvarsof_rec s2).
Proof.
  induction 1; intros.
  +apply Permutation_refl.
  +simpl. destruct x; auto.
  +simpl. destruct x,y; auto.
  +apply Permutation_trans with (gclockvarsof_rec l'); auto.
Qed.

Lemma clockvarsof_rec_permut_map2:
  forall s1 s2,
  Permutation s1 s2 ->
  forall l,
  Permutation (map fst (clockvarsof_rec s1 l)) (map fst (clockvarsof_rec s2 l)).
Proof.
  induction 1; simpl; intros; auto.
  +destruct x,y; auto.
   apply clockvarsof_rec_permut_map1; auto.
   apply clockvars_swap_permut_map; auto.
  +apply Permutation_trans with (map fst (clockvarsof_rec l' l0)); auto.
Qed.

Lemma clockvarsof_permut_map:
  forall l1 l2,
  Permutation l1 l2 ->
  Permutation (map fst (clockvarsof l1)) (map fst (clockvarsof l2)).
Proof.
  unfold clockvarsof. intros.
  rewrite map_app, map_app. apply Permutation_app.
  apply Permutation_map.
  apply gclockvarsof_rec_permut; auto.
  apply clockvarsof_rec_permut_map2; auto.
Qed.

Lemma clockvars_permut:
  forall c l1 l2,
  Permutation l1 l2 ->
  Permutation (clockvars c l1) (clockvars c l2).
Proof.
  destruct c; simpl; intros; auto.
  destruct p. rewrite in_list_perm with (l2:=map fst (map fst l2)).
  destruct (in_list (flagidof b i) (map fst (map fst l2))) eqn:?; auto.
  apply Permutation_app; auto.
  apply Permutation_map; auto. apply Permutation_map; auto.
Qed.

Lemma clockvarsof_rec_permut1:
  forall l l1 l2,
  Permutation l1 l2 ->
  Permutation (clockvarsof_rec l l1) (clockvarsof_rec l l2).
Proof.
  induction l; simpl; intros; auto.
  destruct a; auto.
  eapply IHl; auto.
  eapply clockvars_permut; eauto.
Qed.

Lemma clockvars_swap_permut:
  forall c1 c2 l l0,
  clocks_determ (c2::c1::l) ->
  Permutation (clockvars c1 (clockvars c2 l0)) (clockvars c2 (clockvars c1 l0)).
Proof.
  destruct c1, c2; simpl; intros; auto.
  destruct p. destruct p0.
  destruct (in_list (flagidof b0 i0) (map fst (map fst l0))) eqn:?; auto. 
  +destruct (in_list (flagidof b i) (map fst (map fst l0))) eqn:?; auto.
   rewrite Heqb1. auto.
   rewrite map_app, map_app, in_list_app.
   simpl. rewrite Heqb1. simpl. auto.
  +rewrite map_app, map_app, in_list_app.
   destruct (in_list (flagidof b i) (map fst (map fst l0))) eqn:?; simpl; auto.
   -rewrite Heqb1. auto.
   -simpl. rewrite map_app, map_app, in_list_app.
    rewrite Heqb1. simpl.
    cut (identeq (flagidof b0 i0) (flagidof b i) = identeq (flagidof b i) (flagidof b0 i0)). intros.
    simpl in *. rewrite H0 in *.
    destruct (identeq (flagidof b i) (flagidof b0 i0)) eqn:?; simpl in *; auto.
    *apply Pos.eqb_eq in H0. rewrite H0.
     rewrite H; simpl; auto.
    *repeat rewrite app_ass. simpl.
     apply Permutation_app; auto.
     constructor 3; auto.
    *rewrite Pos.eqb_sym; auto.
Qed.

Lemma clocks_determ_permut:
  forall l1 l2,
  Permutation l1 l2 ->
  clocks_determ l1 -> 
  clocks_determ l2.
Proof. 
  intros. red; intros.
  apply Permutation_sym in H.
  apply H0; auto.
  eapply Permutation_in; eauto.
  eapply Permutation_in; eauto.
Qed.

Lemma clockvarsof_rec_permut2:
  forall l1 l2,
  Permutation l1 l2 ->
  forall l, clocks_determ l1 -> 
  Permutation (clockvarsof_rec l1 l) (clockvarsof_rec l2 l).
Proof.
  induction 1; simpl; intros; auto.
  +apply IHPermutation.
   red; intros. apply H0; simpl; auto.
  +apply clockvarsof_rec_permut1; auto.
   eapply clockvars_swap_permut; eauto.
  +apply Permutation_trans with  (clockvarsof_rec l' l0); auto.
   apply IHPermutation2.
   eapply clocks_determ_permut; eauto.
Qed.

Lemma clockvarsof_permut:
  forall l1 l2,
  Permutation l1 l2 ->
  clocks_determ l1 -> 
  Permutation (clockvarsof l1) (clockvarsof l2).
Proof.
  unfold clockvarsof. intros.
  apply Permutation_app.
  apply gclockvarsof_rec_permut; auto.
  apply clockvarsof_rec_permut2; auto.
Qed.

Lemma clockvarsof_rec_cons_permut:
  forall l c l1,
  exists l2, Permutation (clockvarsof_rec (l++c::nil) l1) (l2 ++ clockvarsof_rec l l1).
Proof.
  induction l; simpl; intros; auto.
  destruct c; simpl.
  +exists nil; simpl; auto.
  +destruct p. destruct (in_list _ _).
   -exists nil; auto.
   -exists ((flagidof b i, type_bool, (b, i) :: c) :: nil).
    apply Permutation_app_swap; auto.
Qed.

Lemma clockvarsof_cons_permut:
  forall c l,
  exists l1, Permutation (map fst (clockvarsof (c :: l))) (map fst (l1 ++ clockvarsof l)).
Proof.
  unfold clockvarsof. intros.
  destruct gclockvarsof_rec_cons_eq with c l as [l2 ?].
  rewrite H.
  destruct clockvarsof_rec_cons_permut with l c (@nil (ident*type*clock)) as [l3 ?].
  exists (l2 ++ l3). repeat rewrite app_ass.
  repeat rewrite map_app with (l:=l2). apply Permutation_app; auto.
  apply Permutation_trans with (map fst (gclockvarsof_rec l ++ l3 ++ clockvarsof_rec l nil)).
  rewrite map_app, map_app. apply Permutation_app; auto.
  apply Permutation_trans with (map fst (clockvarsof_rec (l ++ c :: nil) nil)); auto.
  eapply clockvarsof_rec_permut_map2; eauto.
  change (c :: l) with ((c::nil)++l).
  apply Permutation_app_swap; auto. apply Permutation_map; auto. 
  repeat rewrite <-app_ass.
  apply Permutation_map. apply Permutation_app; auto.
  apply Permutation_app_swap; auto.
Qed.

Lemma clockvars_type_bool:
  forall ty c l1,
  In ty (map snd (map fst (clockvars c l1))) ->
  (forall ty : type, In ty (map snd (map fst l1)) -> ty = type_bool) ->
  ty = type_bool.
Proof.
  intros. destruct c; simpl in *; auto.
  destruct p. destruct (in_list _ _); simpl in *; auto.
  rewrite map_app, map_app in *. simpl in *.
  apply in_app_or in H.
  destruct H; simpl in *; auto.
  destruct H; try tauto; auto.
Qed.

Lemma clockvarsof_rec_type_bool:
  forall l l1 ty,
  In ty (map snd (map fst (clockvarsof_rec l l1))) ->
  (forall ty, In ty (map snd (map fst l1)) -> ty = type_bool) ->
  ty = type_bool.
Proof.
  induction l; simpl; intros; auto.
  eapply IHl; eauto; intros.
  eapply clockvars_type_bool; eauto.
Qed.

Lemma gclockvarsof_rec_type_bool:
  forall l ty,
  In ty (map snd (map fst (gclockvarsof_rec l))) ->
  ty = type_bool.
Proof.
  induction l; simpl; intros.
  tauto.
  destruct a; simpl in *; auto.
  destruct H; try tauto. auto.
Qed.

Lemma clockvarsof_type_bool:
  forall l ty,
  In ty (map snd (map fst (clockvarsof l))) ->
  ty = type_bool.
Proof.
  unfold clockvarsof. intros.
  rewrite map_app, map_app in H.
  apply in_app_or in H. destruct H.
  eapply gclockvarsof_rec_type_bool; eauto.
  eapply clockvarsof_rec_type_bool; eauto.
  simpl. tauto.
Qed.

Lemma ids_norepet_instid:
  forall f, ids_norepet f ->
  list_norepet (map instid (instidof (nd_stmt f))).
Proof.
  intros. destruct H as [? [? ?]].
  apply list_norepet_app in H0.
  destruct H0 as [? [? ?]]. auto.
Qed.

Lemma ids_norepet_instid_permut:
  forall f ss, ids_norepet f ->
  Permutation (nd_stmt f) ss ->
  list_norepet (map instid (instidof ss)).
Proof.
  intros.
  apply list_norepet_permut with (map instid (instidof (nd_stmt f))); auto.
  apply ids_norepet_instid; auto.
  apply Permutation_map. apply flat_map_permutation; auto.
Qed.

Lemma has_for_range:
  forall s, 0 <= has_for s <=1.
Proof.
  destruct s; simpl; try omega.
Qed.

Lemma has_fors_range:
  forall s, 0 <= has_fors s <=1.
Proof.
  induction s; simpl; try omega.
  destruct a.
  destruct (zlt _ _); try omega.
  generalize (has_for_range s0). intros.
  destruct (zle (has_for s0) (has_fors s)).
  rewrite Z.max_r; omega.
  rewrite Z.max_l; omega.
Qed.

Lemma mkloopmapw_norepet:
  forall l, list_norepet (map fst (mkloopmapw l)).
Proof.
  unfold mkloopmapw. intros.
  destruct (has_fors l); simpl.
  +constructor.
  +repeat constructor; auto.
  +repeat constructor; auto.
Qed.

Lemma mkloopmapw_range:
  forall l a, In a (mkloopmapw l) ->
  a = (ACG_I, type_int32s).
Proof.
  unfold mkloopmapw. intros l.
  destruct (has_fors l); simpl; intros; try tauto.
  +destruct H; auto. tauto.
  +destruct H; auto. tauto.
Qed.

Lemma mkloopmapw_idrange:
  forall l id, In id (map fst (mkloopmapw l)) ->
  id = ACG_I.
Proof.
  intros. apply in_map_iff in H.
  destruct H as [? [? ?]]. subst.
  apply mkloopmapw_range in H0.
  subst; auto.
Qed.

Lemma mkloopmapw_disjoint:
  forall s l,
  list_disjoint (ACG_I::nil) l ->
  list_disjoint (map fst (mkloopmapw s)) l.
Proof.
  intros. red; intros.
  apply H; auto.
  apply mkloopmapw_idrange in H0.
  destruct H0; subst; simpl; auto.
Qed.

Lemma has_fors_loop_in:
  forall l, 0 < has_fors l ->
  In (ACG_I, type_int32s) (mkloopmapw l).
Proof.
  induction l; simpl; intros.
  omega.
  unfold mkloopmapw. simpl.
  destruct a.
  destruct (zlt (has_for s) 1); simpl; auto.
  destruct (Z.max (has_for s) (has_fors l)); try omega; simpl; auto.
Qed.

Lemma ids_norepet_clockfbyids_norepet:
  forall f, ids_norepet f ->
  list_norepet (map fst (map fst (clockvarsof (clocksof (nd_stmt f))) ++ fbyvarsof (nd_stmt f))).
Proof.
  intros.
  destruct H as [? [? ?]].
  apply list_norepet_app in H0.
  destruct H0 as [? [? ?]]; auto.
Qed.

Lemma deps_of_stmts_simpl_app:
  forall l1 l2,
  deps_of_stmts_simpl (l1 ++ l2) = deps_of_stmts_simpl l1 ++ deps_of_stmts_simpl l2.
Proof.
  induction l1; simpl; intros; try rewrite IHl1; auto.
Qed.

Lemma nodup_lids_appa: forall (a: depend)(l: list depend),
  nodup_lids (a :: l)  ->
  nodup_lids l.
Proof.
  unfold nodup_lids. simpl. intuition. 
  apply list_norepet_app in H. intuition.
Qed.
    
Lemma nodup_lids_sube: forall (l1 l2: list depend),
  nodup_lids (l1 ++ l2)  ->
  nodup_lids l1.
Proof.
  unfold nodup_lids. intuition.
  rewrite flat_map_app in H. apply list_norepet_app in H. intuition.
Qed.
  
Lemma nodup_lids_perm: forall (l1 l2: list depend),
  Permutation l1 l2 ->
  nodup_lids l1 ->
  nodup_lids l2.
Proof.
  unfold nodup_lids. intros.
  eapply list_norepet_permut; eauto. 
  apply flat_map_permutation;trivial.
Qed.

Lemma topo_sorted_eqs_simpl:
  forall eql,
  topo_sorted (deps_of_stmts eql) <->
  topo_sorted (deps_of_stmts_simpl eql).
Proof.
  intros. split; intros; 
  [ apply depend_toposorted with (deps_of_stmts eql) |
    apply depend_toposorted with (deps_of_stmts_simpl eql)]; trivial;
  unfold deps_of_stmts_simpl; unfold deps_of_stmts;
  repeat rewrite map_map; simpl; 
  set (idll:= map (fun eq => lidl_of_s (fst eq)) eql);
  rewrite <- seq_nth_fun_equal with _ _ (fun eq => mkdepend (lidl_of_s (fst eq)) (ridl_of_sc eq) O) eql (Sskip,nil);
  trivial.
Qed.

Definition is_assign(s: stmt*clock) : Prop :=
  match s with
  | (Sassign _ (Expr _), nil) => True
  | _ => False
  end.

Lemma lidl_of_fs_incl:
  forall s, incl (flat_map (fun s => lidl_of_s (fst s)) (initstmtsof1 s)) (lidl_of_fs s).
Proof.
  induction s; simpl; try incl_tac.
Qed.

Lemma ridl_of_fs_incl:
  forall s, incl (flat_map ridl_of_sc (initstmtsof1 s)) (ridl_of_fs s).
Proof.
  induction s; simpl; try rewrite <-app_nil_end; try incl_tac.
Qed.

Lemma initstmtsof_is_assign:
  forall s, Forall is_assign (initstmtsof1 s).
Proof.
  induction s; simpl; repeat constructor; simpl; auto.
Qed.

Definition is_timestmt(s: stmt) : Prop :=
  match s with
  | Sfby _ _ _ _ => True
  | Sfbyn _ _ _ _ _ => True
  | Sarrow _ _ _ => True
  | Scurrent _ _ _ _ => True
  | Spre _ _ _ => True
  | ScurrentR _ _ _ _ _ => True
  | _ => False
  end.

Lemma clockvarsof_cons_nil:
  forall cks s,
  is_timestmt s ->
  clockvarsof (clockof (s,cks)) = (flagid cks, type_bool, cks)::nil.
Proof.
  unfold clockvarsof.
  destruct s; intros; try tauto;
  destruct cks; simpl; auto;
  destruct p0; auto.
  destruct p1;auto.
Qed.