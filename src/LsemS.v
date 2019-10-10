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
Require Import Maps.
Require Import Cltypes.
Require Import List.
Require Import Lvalues.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.
Require Import Lustre.
Require Import LustreS.
Require Import Lenv.
Require Import LsemT.
Require Import Lsem.

Section SEMANTICS.

Variable p: program.
Variable gc: locenv.

Inductive eval_node: env -> env -> ident*node -> list val -> list val -> Prop :=
  | exec_node: forall te te1 te2 eh eh1 eh3 se se1 vrs vas nid f,
      alloc_variables empty_locenv (mkloopmapw (nd_stmt f) ++ allvarsof f) te ->
      ids_norepet f ->
      locenv_setvars te f.(nd_args) vas te1 -> 
      eval_stmts (nd_kind f) te1 (mkenv eh se) te2 (mkenv eh1 se1) f.(nd_stmt) -> 
      eval_fbyeqs gc te2 eh1 eh3 (eqtsof f.(nd_stmt)) ->
      locenv_getvars te2 f.(nd_rets) vrs -> 
      has_types vrs (map snd (nd_rets f)) ->
      eval_node (mkenv eh se) (mkenv eh3 se1) (nid,f) vas vrs 

with eval_stmts: bool -> locenv -> env -> locenv -> env -> list (stmt*clock) -> Prop :=
  | eval_stmts_nil: forall nk te e,
      eval_stmts nk te e te e nil
  | eval_stmts_cons_true: forall nk te te1 te2 e e1 e2 s ss cks,
      eval_clock_conds gc te (rev (clock_conds cks)) true ->
      eval_stmt nk te e te1 e1 s cks ->
      eval_stmts nk te1 e1 te2 e2 ss ->
      eval_stmts nk te e te2 e2 ((s,cks) :: ss)
  | eval_stmts_cons_false: forall nk te te1 e e1 s ss cks,
      eval_clock_conds gc te (rev (clock_conds cks)) false ->
      eval_stmts nk te e te1 e1 ss ->
      eval_stmts nk te e te1 e1 ((s, cks) :: ss)

with eval_stmt: bool -> locenv -> env -> locenv-> env -> stmt -> clock -> Prop :=
  | eval_Sassign: forall nk te te' e lh a v v' cks,
      eval_expr gc te a (snd lh) v ->
      eval_cast v (snd lh) v' ->
      locenv_setlvar gc te (lvarof lh) v' te' ->
      eval_stmt nk te e te' e (Sassign lh a) cks
  | eval_Scall: forall nk te te' eh se se' args vargs vrets cdef lhs cks,
      eval_sexps gc te args vargs -> 
      eval_apply nk te se se' (map typeof args) vargs Int.zero cdef (map snd lhs) vrets ->
      locenv_setvars te lhs vrets te' ->
      eval_stmt nk te (mkenv eh se) te' (mkenv eh se') (Scall lhs cdef args) cks
  | eval_Sfor_start: forall nk te te1 te2 te3 e e1 s j cks,
      eval_stmts nk te e te1 e (initstmtsof2 s) ->
      eval_eqf gc te1 te2 loop_init ->
      eval_stmt nk te2 e te3 e1 (Sfor false s j) cks ->
      eval_stmt nk te e te3 e1 (Sfor true s j) cks
  | eval_Sfor_false: forall nk te e s j cks,
      eval_sexp gc te (loop_cond j) Vfalse ->
      eval_stmt nk te e te e (Sfor false s j) cks
  | eval_Sfor_loop: forall nk te te1 te2 te3 e e1 e2 s j cks,
      eval_sexp gc te (loop_cond j) Vtrue ->
      eval_hstmt nk te e te1 e1 s ->
      eval_eqf gc te1 te2 loop_add ->
      eval_stmt nk te2 e1 te3 e2 (Sfor false s j) cks ->
      eval_stmt nk te e te3 e2 (Sfor false s j) cks
  | eval_Sarydif_nil: forall nk te e lh i cks, 
      eval_stmt nk te e te e (Sarydif lh i nil) cks
  | eval_Sarydif_cons: forall nk te te1 te2 e lid aid ty num i a al v v' cks, 
      eval_sexp gc te a v ->
      typeof a = ty ->
      eval_cast v ty v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid ty num)) (Sconst (Cint i) type_int32s) ty) v' te1 ->
      eval_stmt nk te1 e te2 e (Sarydif (lid,Tarray aid ty num) (Int.add i Int.one) al) cks ->
      eval_stmt nk te e te2 e (Sarydif (lid,Tarray aid ty num) i (a :: al)) cks
  | eval_Smix: forall nk te te1 te2 e lid ty a1 lis a3 o v3 v cks, 
      eval_lindexs gc te (typeof a3) ty lis Int.zero o ->
      eval_sexp gc te a3 v3 ->
      eval_stmt nk te e te1 e (Sassign (lid,ty) (Expr a1)) cks ->
      eval_cast v3 (typeof a3) v -> 
      store_env (typeof a3) te1 lid o v te2 ->
      eval_stmt nk te e te2 e (Smix (lid,ty) a1 lis a3) cks 
  | eval_Sstruct_nil: forall nk te e lh cks,
      eval_stmt nk te e te e (Sstruct lh Fnil nil) cks
  | eval_Sstruct_cons: forall nk te te1 te2 e lid ty i t ftl a al v v' cks,
      eval_sexp gc te a v ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Sfield (Svar lid ty) i t) v' te1 ->
      typeof a = t ->
      eval_stmt nk te1 e te2 e (Sstruct (lid,ty) ftl al) cks ->
      eval_stmt nk te e te2 e (Sstruct (lid,ty) (Fcons i t ftl) (a::al)) cks
  | eval_Sskip: forall nk te e cks,
      eval_stmt nk te e te e Sskip cks
  | eval_Sfby_cycle_1: forall te te1 eh se lh id a1 a2 v2 v cks,
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) Vtrue ->
      eval_sexp gc te a2 v2 ->
      snd lh = typeof a2 ->
      eval_cast v2 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2) cks
  | eval_Sfby_cycle_n: forall te te1 eh se lh id a1 a2 v1 v cks,
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) Vfalse ->
      eval_sexp empty_locenv eh (Svar id (typeof a1)) v1 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2) cks
  | eval_Sfbyn_cycle_1: forall te te1 eh eh1 eh2 se lh id1 id2 aid sa aty i a1 a2 v1 v2 v cks,
      Tarray aid (typeof a1) (Int.unsigned i) = aty ->
      Svar id1 (make_fbyn_type id2 aty) = sa ->
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) Vtrue->
      eval_sexp gc te a2 v2 ->
      eval_fbyn_init gc id1 id2 aid (typeof a2) Int.zero i v2 eh eh1 ->
      eval_eqf gc eh1 eh2 (Sfield sa FBYIDX type_int32s, Sconst (Cint Int.zero) type_int32s) ->
      eval_sexp empty_locenv eh2 (fbyn_aryacc sa (typeof a1) aty) v1 ->
      snd lh = typeof a2 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh2 se) (Sfbyn lh (id1,id2,aid) i a1 a2) cks
  | eval_Sfbyn_cycle_n: forall te te1 eh se lh id1 id2 aid sa aty i a1 a2 v1 v cks,
      Tarray aid (typeof a1) (Int.unsigned i) = aty ->
      Svar id1 (make_fbyn_type id2 aty) = sa ->
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) Vfalse->
      eval_sexp empty_locenv eh (fbyn_aryacc sa (typeof a1) aty) v1 ->
      snd lh = typeof a2 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfbyn lh (id1,id2,aid) i a1 a2) cks
  | eval_Sarrow: forall te te1 eh se lh a1 a2 v b cks,
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) v ->
      bool_val v type_bool = Some b ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sassign lh (Expr (if b then a1 else a2))) cks ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sarrow lh a1 a2) cks
  | eval_Scurrent_true: forall te te1 eh se lh id a a1 v1 v cks,
      eval_sexp gc te a Vtrue ->
      eval_sexp gc te a1 v1 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      typeof a = type_bool ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Scurrent lh id a a1) cks
  | eval_Scurrent_false: forall te te1 eh se lh id a a1 cks,
      eval_sexp gc te a Vfalse ->
      typeof a = type_bool ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Spre lh id a1) cks ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Scurrent lh id a a1) cks
  | eval_Spre_cycle_1: forall te te1 eh se lh id a1 v2 v cks,
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) Vtrue ->
      eval_pre (typeof a1) v2 ->
      snd lh = typeof a1 ->
      eval_cast v2 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Spre lh id a1) cks
  | eval_Spre_cycle_n: forall te te1 eh se lh id a1 v1 v cks,
      eval_sexp empty_locenv eh (Svar (flagid cks) type_bool) Vfalse ->
      eval_sexp empty_locenv eh (Svar id (typeof a1)) v1 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Spre lh id a1) cks
  | eval_ScurrentR_true: forall te te1 eh se lh id a a1 a2 v1 v cks,
      eval_sexp gc te a Vtrue ->
      eval_sexp gc te a1 v1 ->
      snd lh = typeof a1 ->
      eval_cast v1 (snd lh) v ->
      locenv_setlvar gc te (lvarof lh) v te1 ->
      typeof a = type_bool ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (ScurrentR lh id a a1 a2) cks
  | eval_ScurrentR_false: forall te te1 eh se lh id a a1 a2 cks,
      eval_sexp gc te a Vfalse ->
      typeof a = type_bool ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (Sfby lh id a1 a2) cks ->
      eval_stmt true te (mkenv eh se) te1 (mkenv eh se) (ScurrentR lh id a a1 a2) cks


with eval_hstmt: bool -> locenv -> env -> locenv -> env-> hstmt -> Prop :=
   | eval_Hmaptyeq: forall nk te te1 e lid aid aid1 t num a1 a2 (k:bool) b, 
      typeof a1 = Tarray aid1 t num ->
      eval_typecmp gc te (Saryacc a1 (Svar ACG_I type_int32s) t) (Saryacc a2 (Svar ACG_I type_int32s) t) b ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid type_bool num)) (Svar ACG_I type_int32s) type_bool) (if (if k then b else negb b) then Vtrue else Vfalse) te1 ->
      eval_hstmt nk te e te1 e (Hmaptycmp (lid, (Tarray aid type_bool num)) k a1 a2) 
  | eval_Hmapary: forall nk te e te1 lid aid t num op a1 a2 v v',
      eval_sexp gc te (Sbinop op (Saryacc a1 (Svar ACG_I type_int32s) t) (Saryacc a2 (Svar ACG_I type_int32s) t) t) v ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t num)) (Svar ACG_I type_int32s) t) v' te1 ->
      eval_hstmt nk te e te1 e (Hmapary (lid, (Tarray aid t num)) op a1 a2)
  | eval_Hmapunary: forall nk te te1 e lid aid t1 t2 num op a1 v v',
      typeof a1 = Tarray aid t1 num ->
      prefix_unary_type op t1 t2 ->
      eval_sexp gc te (trans_prefix_unary_expr op (Saryacc a1 (Svar ACG_I type_int32s) t1) t2) v ->
      eval_cast v t2 v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t2 num)) (Svar ACG_I type_int32s) t2) v' te1 ->
      eval_hstmt nk te e te1 e (Hmapunary (lid, (Tarray aid t2 num)) op a1)
  | eval_Hflodary: forall nk te te1 e lid t op a1 a2,
      eval_eqf gc te te1 (Svar lid t, Sbinop op (Svar lid t) (Saryacc a2 (Svar ACG_I type_int32s) t) t) ->
      eval_hstmt nk te e te1 e (Hfoldary (lid, t) op a1 a2)
  | eval_Hflodunary: forall nk te te1 e lid t op a1,
      eval_eqf gc te te1 (Svar lid t, Sunop op (Svar lid t) t) ->
      eval_hstmt nk te e te1 e (Hfoldunary (lid, t) op a1)
  | eval_Hflodcast: forall nk te te1 e lid t a1,
      eval_eqf gc te te1 (Svar lid t, Scast (Svar lid t) t) ->
      eval_hstmt nk te e te1 e (Hfoldcast (lid, t) a1 t)
  | eval_Harydef: forall nk te te1 e lid aid t num a v v', 
      eval_sexp gc te a v ->
      typeof a = t ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t num)) (Svar ACG_I type_int32s) t) v' te1 ->
      eval_hstmt nk te e te1 e (Harydef (lid,Tarray aid t num) a)
  | eval_Haryslc: forall nk te te1 e lid aid t num a j v v',
      eval_sexp gc te (Saryacc a (Sbinop Oadd (Sconst (Cint j) type_int32s) (Svar ACG_I type_int32s) type_int32s) t) v ->
      eval_cast v t v' ->
      locenv_setlvar gc te (Saryacc (Svar lid (Tarray aid t num)) (Svar ACG_I type_int32s) t) v' te1 ->
      eval_hstmt nk te e te1 e (Haryslc (lid, Tarray aid t num) a j)
  | eval_Hboolred_true: forall nk te te1 e lid a,
      eval_sexp gc te (Saryacc a (Svar ACG_I type_int32s) type_bool) Vtrue ->
      eval_eqf gc te te1 (Svar lid type_int32s, self_add lid) ->
      eval_hstmt nk te e te1 e (Hboolred (lid, type_int32s) a)
  | eval_Hboolred_false: forall nk te e lid a,
      eval_sexp gc te (Saryacc a (Svar ACG_I type_int32s) type_bool) Vfalse ->
      eval_hstmt nk te e te e (Hboolred (lid, type_int32s) a)
  | eval_Hmapcall: forall nk te te1 eh se se1 lhs cdef args atys rtys i vl vas vrs,
      eval_sexps gc te args vl -> 
      eval_sexp gc te (Svar ACG_I type_int32s) (Vint i) ->
      locenv_getarys i (map typeof args) atys vl vas ->
      eval_apply nk te se se1 atys vas i cdef rtys vrs ->
      locenv_setarys gc (Svar ACG_I type_int32s) te lhs rtys vrs te1 ->
      eval_hstmt nk te (mkenv eh se) te1 (mkenv eh se1) (Hmapcall lhs cdef args)
  | eval_Hfillcall: forall nk te te1 te2 te3 eh se se1 lid tid ty lhs cdef i v init vret vrs tys,
      eval_stmt nk te (mkenv eh se) te1 (mkenv eh se) (Sassign (tid,ty) (Expr (Svar lid ty))) nil->
      eval_sexp gc te1 (Svar tid ty) v ->
      eval_sexp gc te1 (Svar ACG_I type_int32s) (Vint i) ->
      eval_apply nk te1 se se1 (ty::nil) (v::nil) i cdef (ty::tys) (vret::vrs) ->
      locenv_setlvar gc te1 (Svar lid ty) vret te2 ->
      locenv_setarys gc (Svar ACG_I type_int32s) te2 lhs tys vrs te3 ->
      eval_hstmt nk te (mkenv eh se) te3 (mkenv eh se1) (Hfillcall (lid,ty) (tid,ty) lhs cdef init)
  | eval_Hredcall: forall nk te te1 te2 eh se se1 lid tid ty cdef args i v atys vl init vargs vret,
      eval_stmt nk te (mkenv eh se) te1 (mkenv eh se) (Sassign (tid,ty) (Expr (Svar lid ty))) nil->
      eval_sexp gc te1 (Svar tid ty) v ->
      eval_sexps gc te1 args vl -> 
      eval_sexp gc te1 (Svar ACG_I type_int32s) (Vint i) ->
      locenv_getarys i (map typeof args) atys vl vargs ->
      eval_apply nk te1 se se1 (ty::atys) (v::vargs) i cdef (ty::nil) (vret::nil) ->
      locenv_setlvar gc te1 (Svar lid ty) vret te2 ->
      eval_hstmt nk te (mkenv eh se) te2 (mkenv eh se1) (Hredcall (lid,ty) (tid,ty) cdef init args)
  | eval_Hmapfoldcall: forall nk te te1 te2 te3 eh se se1 lid tid ty lhs cdef args i v atys vl init vargs vret vrs tys,
      eval_stmt nk te (mkenv eh se) te1 (mkenv eh se) (Sassign (tid,ty) (Expr (Svar lid ty))) nil ->
      eval_sexp gc te1 (Svar tid ty) v ->
      eval_sexps gc te1 args vl -> 
      eval_sexp gc te1 (Svar ACG_I type_int32s) (Vint i) ->
      locenv_getarys i (map typeof args) atys vl vargs ->
      eval_apply nk te1 se se1 (ty::atys) (v::vargs) i cdef (ty::tys) (vret::vrs) ->
      locenv_setlvar gc te1 (Svar lid ty) vret te2 ->
      locenv_setarys gc (Svar ACG_I type_int32s) te2 lhs tys vrs te3 ->
      eval_hstmt nk te (mkenv eh se) te3 (mkenv eh se1) (Hmapfoldcall (lid,ty) (tid,ty) lhs cdef init args) 

with eval_apply: bool -> locenv -> subenv -> subenv -> list type -> list val-> int-> calldef -> list type -> list val -> Prop :=
  | eval_Apply: forall nk fd ef ef' te se se1 cdef i atys rtys vargs vargs' vrets,
      callorder nk (nd_kind (snd fd)) = true ->
      call_func (node_block p) cdef fd ->
      map snd (nd_args (snd fd)) = atys ->
      map snd (nd_rets (snd fd)) = rtys ->
      eval_casts vargs atys vargs' ->
      call_env cdef i se se1 ef ef' ->
      eval_node ef ef' fd vargs' vrets -> 
      te ! (callid cdef) = None ->
      eval_apply nk te se se1 atys vargs i cdef rtys vrets
.

Scheme eval_node_ind2 := Minimality for eval_node Sort Prop
  with eval_stmts_ind2 := Minimality for eval_stmts Sort Prop
  with eval_stmt_ind2 := Minimality for eval_stmt Sort Prop
  with eval_hstmt_ind2 := Minimality for eval_hstmt Sort Prop
  with eval_apply_ind2 := Minimality for eval_apply Sort Prop. 

End SEMANTICS.
