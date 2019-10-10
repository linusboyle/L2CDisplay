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

(** Common definitions for LustreS, LustreR and LustreF. *)

Require Import List.
Require Import Coqlib.
Require Import AST.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Cop.
Require Import Ctypes.
Require Import Cltypes.
Require Import Lident.
Require Import Ltypes.
Require Import Lop.

Set Implicit Arguments.

(** Clock 

- If exp = (1 when not ck1 when ck2), then clock of exp is expressed by syntax as below:
       Clock ((true, ck2)::(false, ck1)::nil)
- If exp = 1, then clock of exp is base clock, and is expressed by syntax as below:
       Clock nil
 *)

Definition clock := list (bool * ident).

(** Base clock of Lustre. *)
Definition global_clock : clock := nil.

Definition headof(A: Type)(l: list A)(msg: errmsg): res A :=
  match l with
  | nil => Error msg
  | hd :: tl => OK hd
  end.

Definition flagidof (f: bool) (cid : ident): ident := 
  if f then acg_clock_init cid else acg_clock_init1 cid.

Definition flagid(cks: clock) : ident :=
  match cks with
  | nil => ACG_INIT
  | ((ck,cid) :: _) => flagidof ck cid
  end.

Definition clockvars(cks: clock)(flags: list ((ident*type)*clock)) :=
  let fl := map fst (map fst flags) in
  match cks with
  | nil => flags
  | ((ck,cid) :: _) =>
    let f := flagidof ck cid in
    if in_list f fl then flags else flags ++ (((f , type_bool), cks)::nil)
  end.

Definition sign_compare(s1 s2: signedness) : bool :=
  match s1, s2 with
  | Signed, Signed => true
  | Unsigned, Unsigned => true
  | _ , _ => false
  end.

Definition intsize_compare(i1 i2: intsize) : bool :=
  match i1, i2 with
  | I8, I8 => true
  | I16, I16 => true
  | I32, I32 => true
  | IBool, IBool => true
  | _, _ => false
  end.

Fixpoint type_compare(t1 t2: type): bool :=
  match t1,t2 with
  | Tstruct id1 fld1, Tstruct id2 fld2 => 
    identeq id1 id2 && type_list_compare fld1 fld2
  | Tint i1 s1, Tint i2 s2 => 
    intsize_compare i1 i2 && sign_compare s1 s2 
  | Tfloat F32, Tfloat F32 => true
  | Tfloat F64, Tfloat F64 => true
  | Tarray id1 at1 n1, Tarray id2 at2 n2 => 
    identeq id1 id2 && type_compare at1 at2 && Z.eqb n1 n2
  | _, _ => false 
  end

with type_list_compare(fld1 fld2: fieldlist): bool :=
  match fld1, fld2 with
  | Fnil,Fnil => true
  | Fcons id1 ty1 tl1, Fcons id2 ty2 tl2 => 
    identeq id1 id2 && type_compare ty1 ty2 && type_list_compare tl1 tl2
  | _, _ => false
  end.

Lemma type_compare_eq:
  forall t1 t2,
  type_compare t1 t2 = true ->
  t1 = t2.
Proof.
  intros t1 t2.
  apply (type_ind2 (fun t1 => forall t2, type_compare t1 t2 = true -> t1 = t2)
                   (fun f1 => forall f2, type_list_compare f1 f2 = true -> f1 = f2)).
  +destruct t0; simpl; intros; congruence.
  +destruct t0; simpl; intros; try congruence.
   destruct i, i0, s, s0; simpl in *; congruence.
  +destruct f, t0; simpl; intros; try congruence;
   destruct f; try congruence.
  +destruct t0; simpl; intros; congruence.
  +destruct t0; simpl; intros; try congruence.
   destruct (identeq i i0) eqn:?; simpl in *; try congruence.
   destruct (type_compare t t0) eqn:?; simpl in *; try congruence.
   apply Peqb_eq in Heqb. subst.
   rewrite H with t0; auto.
   apply Z.eqb_eq in H0. subst. auto.
  +destruct t0; simpl; intros; try congruence.
  +destruct t0; simpl; intros; try congruence.
   destruct (identeq i i0) eqn:?; simpl in *; try congruence.
   apply Peqb_eq in Heqb. subst.
   rewrite H with f0; auto.
  +destruct f2; simpl; intros; try congruence.
  +destruct f2; simpl; intros; try congruence.
   destruct (identeq i i0) eqn:?; simpl in *; try congruence.
   destruct (type_compare t t0) eqn:?; simpl in *; try congruence.
   apply Peqb_eq in Heqb. subst.
   rewrite H with t0; auto.
   rewrite H0 with f2; auto.
Qed.

(** Iterator *)

Inductive iterator_operation : Type := 
  | Omap : iterator_operation          (**r or map <suboperatorL> <<INTEGER>> *)
  | Ored: iterator_operation
  | Ofill: iterator_operation
  | Ofillred: iterator_operation.      

(** Pattern of case expr. *)
Record patn: Type :=
  | Pachar: int -> patn
  | Paint: int -> patn
  | Pabool: bool -> patn
  | Paenum: ident -> list ident -> patn
  | Pany: patn.

(** Const expr. *)
Inductive const: Type :=
  | Cint: int -> const
  | Cfloat: float -> const
  | Csingle: float32 -> const
  | Cbool: bool -> const
  | Cenum: ident -> list ident -> const.

(** Simplified expr for LustreS, LustreR and LustreF. *)
Inductive sexp: Type :=
  | Sconst: const -> type -> sexp          (**r const expr *)
  | Svar: ident -> type -> sexp            (**r local variable *)
  | Scvar: ident -> type -> sexp           (**r global const variable *)
  | Ssvar: ident -> type -> sexp           (**r output struct variable *)
  | Savar: ident -> type -> sexp           (**r input variable *)
  | Saryacc: sexp -> sexp -> type -> sexp  (**r access to a index of a array *)
  | Sfield: sexp -> ident -> type -> sexp  (**r access to a member of a struct *)
  | Scast: sexp -> type -> sexp            (**r type cast ([(ty) e]) *)
  | Sunop: unary_operation -> sexp -> type -> sexp (**r unary operation *)
  | Sbinop: binary_operationL -> sexp -> sexp -> type -> sexp. (**r binary operation *)

(** A map to sexp*)
Definition mkvar: Type := ident -> type -> sexp.

(** Extract the type part of a Lustre expression. *)

Definition typeof(a: sexp): type :=
  match a with
  | Sconst _ ty => ty
  | Svar _ ty => ty
  | Scvar _ ty => ty
  | Ssvar _ ty => ty
  | Savar _ ty => ty
  | Saryacc _ _ ty => ty
  | Sfield _ _ ty => ty
  | Scast _ ty => ty
  | Sunop _ _ ty => ty
  | Sbinop _ _ _ ty => ty
  end.

Fixpoint get_expids (e: sexp): list ident :=
  match e with
  | Sconst _ _ => nil
  | Svar id _  => id :: nil
  | Scvar id _  => id :: nil
  | Ssvar id _  => id :: nil
  | Savar id _  => id :: nil
  | Sunop _ e1 _ => get_expids e1
  | Sbinop _ e1 e2 _ => get_expids e1 ++ get_expids e2
  | Saryacc e1 a _ => get_expids e1 ++ get_expids a            
  | Sfield e1 _ _ => get_expids e1
  | Scast e1 _ => get_expids e1
  end.

Definition get_expsids (l: list sexp): list ident :=
  flat_map get_expids l.

Fixpoint get_lids (e: sexp): list ident :=
  match e with
  | Svar id _  => id :: nil
  | Scvar id _  => id :: nil
  | Ssvar id _  => id :: nil
  | Savar id _  => id :: nil
  | Saryacc e1 a _ => get_lids e1           
  | Sfield e1 _ _ => get_lids e1 
  | _ => nil
  end.

Fixpoint lid_disjoint(e: sexp): Prop :=
  match e with
  | Svar id _  => id <> ACG_I
  | Ssvar id _  => id <> ACG_I
  | Saryacc e1 (Svar id _) _ => lid_disjoint e1 /\ ACG_I = id          
  | Sfield e1 _ _ => lid_disjoint e1
  | _ => False
  end.

Definition trans_patn(f: sexp -> sexp)(pa: patn * sexp): patn * sexp:=
  (fst pa, f (snd pa)).

Definition trans_patns(f: sexp -> sexp)(l: list (patn * sexp)): list (patn * sexp):=
  map (trans_patn f) l.

Definition arystr_sexps(al: list sexp): list sexp := 
  filter (fun a => is_arystr (typeof a)) al.

Definition trans_bool(b: bool) := if b then Int.one else Int.zero.

Lemma get_lids_expids_incl:
  forall s, incl (get_lids s) (get_expids s).
Proof.
  induction s; simpl; red; intros; try tauto.
  apply in_or_app; auto. auto.
Qed.

Inductive lindex: Type :=
  | Label : ident -> lindex
  | Index : sexp -> lindex.

Definition get_lindexid (li: lindex) : list ident :=
  match li with
  | Label id => id :: nil
  | Index a => get_expids a
  end.

Definition get_lindexids (li: list lindex) : list ident :=
  flat_map get_lindexid li.

Definition loop_cond (j: int) :=
  Sbinop Olt (Svar ACG_I type_int32s) (Sconst (Cint j) type_int32s) type_bool. 

Definition self_add(id: ident):= 
  Sbinop Oadd (Svar id type_int32s) (Sconst (Cint Int.one) type_int32s) type_int32s.

Definition lvarof (lh: ident*type) := Svar (fst lh) (snd lh).

Definition params:= list (ident*type).        
Definition lhs:= list (ident*type).        
Definition init_datas:= list init_data.    
Definition eqf:= prod sexp sexp.            

Inductive eqt : Type :=
  | Eqt_assign: eqf -> eqt
  | Eqt_counter: eqf -> eqt.

Definition clock_cond (ck: bool*ident): sexp :=
  let cond := Svar (snd ck) type_bool in
  if (fst ck) then cond else Sunop Onotbool cond type_bool.

Definition clock_conds(cks: clock): list sexp :=
  map clock_cond cks.

Definition clockresetsof(flags : list ((ident*type)*clock)): list (eqt*list sexp) :=
  map (fun v => (Eqt_assign (lvarof (fst v), Sconst (Cbool false) type_bool), clock_conds (snd v))) flags.

Definition lidsof_eqt(a: eqt*list sexp): list ident :=
  match fst a with
  | Eqt_assign (a, _) => get_lids a
  | Eqt_counter (a, _ ) => get_lids a
  end.

Definition loop_init := 
  (Svar ACG_I type_int32s, Sconst (Cint Int.zero) type_int32s).

Definition loop_add :=
  (Svar ACG_I type_int32s, self_add ACG_I).

Definition make_fbyn_type(pid: ident)(aty: type): type :=
  Tstruct pid (Fcons FBYIDX type_int32s (Fcons FBYITEM aty Fnil)).

Definition mod_add(a: sexp)(i: int) :=
  (a, Sbinop Omod (Sbinop Oadd a (Sconst (Cint Int.one) type_int32s) type_int32s) (Sconst (Cint i) type_int32s) type_int32s).

Definition index_incr(sa: sexp)(i: int) :=
  mod_add (Sfield sa FBYIDX type_int32s) i.

Definition fbyn_aryacc(sa: sexp)(ty aty:type) :=
  let ei := Sfield sa FBYIDX type_int32s in 
  let ea := Sfield sa FBYITEM aty in 
  Saryacc ea ei ty. (*fs.items[fs.idx];*)

Section NODE.

Variable S: Type.

Record general_node: Type := mknode {
  nd_kind: bool;                 (**r node kind. *)
  nd_args: params;               (**r input parameters. *)
  nd_rets: params;               (**r output parameters. *)
  nd_flags: params;
  nd_svars: params;              (**r tempo variables. *)
  nd_vars: params;               (**r local variables. *)
  nd_stmt: S;                    (**r statement. *) 
  nd_sid: ident;                 (**r name of output struct. *)
  nd_fld: fieldlist;              (**r fieldlist of output struct. *)
  nd_eqt: list (eqt*list sexp)
}.

Definition flagvarsof(flags: list ident): params :=
  map (fun id => (id, type_bool)) flags.

Definition mknstruct(f: general_node) :=
  Tstruct (nd_sid f) (nd_fld f).

Definition allvarsof(f: general_node) := 
  (nd_vars f ++ nd_args f) ++ nd_rets f.

Definition allidsof(f: general_node) := 
  map fst (allvarsof f).

Definition lvarsof(f: general_node) := 
  nd_vars f ++ nd_args f.

Definition svarsof(f: general_node) := 
  nd_rets f ++ (nd_flags f ++ nd_svars f).

Record calldef : Type := mkcalldef {
  cakind: bool;              (**r call kind. *)
  instid: ident;             (**r name of call instance. *)
  callid: ident;             (**r name of call node. *)
  callnum: option int;       (**r length of call instance array. *)
  csid: ident;               (**r name of call struct. *)
  cfield: fieldlist;         (**r fieldlist of call struct. *)
  argtys: list type;         (**r type list of input parameters in call node. *)
  rettys: list (ident*type)  (**r output parameters in call node. *)
}.

Definition mkcstruct(c: calldef) :=
  Tstruct (csid c) (cfield c).

Definition intof_opti(oi: option int): int :=
  match oi with
  | Some i => i
  | None => Int.one
  end.

Definition cons_inst(c: calldef): list calldef :=
  if (cakind c) then c:: nil else nil.

Definition callorder(nk fk: bool): bool :=
  match nk, fk with
  | false, true => false
  | _, _ => true
  end.

Lemma cons_inst_incl:
  forall c l, cakind c = true ->
  incl (cons_inst c) l ->
  In c l.
Proof.
  unfold cons_inst. intros.
  apply H0. rewrite H; simpl; auto.
Qed.

Lemma callorder_true:
  forall b, callorder b true = true -> b = true.
Proof.
  destruct b; simpl; auto.
Qed.

Definition call_func(ge: list (ident*general_node))(cdef: calldef)(fd: ident*general_node) : Prop :=
  find_funct ge (callid cdef) = Some fd
    /\ cakind cdef = nd_kind (snd fd)
    /\ 0 < Int.unsigned (intof_opti (callnum cdef)) <= Int.max_signed.

Definition call_node(ge: list (ident*general_node))(nid:ident)(cdef: calldef)(nd fd: ident*general_node) : Prop :=
  find_funct ge nid = Some nd 
     /\ callorder (nd_kind (snd nd)) (nd_kind (snd fd)) = true 
     /\ call_func ge cdef fd.

Lemma call_func_app:
  forall (l1: list (ident*general_node)) l2 cdef fd,
  call_func l1 cdef fd ->
  call_func (l1 ++ l2) cdef fd.
Proof.
  unfold call_func. intuition.
  apply find_funct_app; auto.
Qed.

Lemma call_func_in:
  forall l cdef (fd: ident*general_node),
  call_func l cdef fd ->
  In fd l.
Proof.
  unfold call_func.
  intuition; try eapply find_funct_in2; eauto.
Qed.

Lemma call_func_disjoint:
  forall l1 l2 cdef (fd: ident*general_node),
  call_func (l1 ++ l2) cdef fd ->
  list_disjoint (callid cdef :: nil) (map (@fst ident general_node) l2) ->
  call_func l1 cdef fd.
Proof.
  unfold list_disjoint, call_func. intuition.
  eapply find_funct_app_notin; eauto.
  red. intros. eapply H0; simpl; eauto.
Qed. 

End NODE.

Section PROGRAM.

Variable F: Type.

(** Programs *)

Record general_program: Type := mkprogram {
  type_block: list (ident * type);           
  const_block: list (ident * globvar type); 
  node_block: list (ident*F);               
  node_main: ident                        
}.

Definition globidsof(p: general_program): list ident :=
  (map fst (type_block p) ++ map fst (const_block p)) 
   ++ map fst (node_block p).

Definition globidspltof(p: general_program): list ident :=
  map fst (const_block p) ++ map fst (node_block p).
  
End PROGRAM.
