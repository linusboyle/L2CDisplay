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

(** Translate typedef and toposort types. *)

Require Import Coqlib.
Require Import Ctypes.
Require Import Cltypes.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Tree.
Require Import Lident.
Require Import Toposort.
Require Import String.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Section TRANSLATION.

Definition typenv:= list typeStmt.

Fixpoint find_kind(te: typenv)(id: AST.ident): res kind :=
  match te with
  | nil =>  Error (msg (String.append (extern_atom id) " canot be found in typenv!!"))
  | TypeStmt tid k :: te' =>
    if identeq id (key tid) then 
      OK k
    else find_kind te' id
  end.

Fixpoint trans_kind(te: typenv)(k: kind): res kind :=
  match k with  
  | AtomType a => OK (AtomType a)
  | Struct f => 
    do f' <- trans_fieldlist te f;
    OK (Struct f')
  | Array k e => 
    do k' <- trans_kind te k;
    OK (Array k' e)
  | EnumType idl => OK (EnumType idl)
  | TypeDef id => find_kind te (key id) 
  end

with trans_fieldlist(te: typenv)(f: fieldlist): res fieldlist :=
  match f with
  | Fnil => OK Fnil
  | Fcons id k ftl => 
    do k' <- trans_kind te k;
    do ftl' <- trans_fieldlist te ftl;
    OK (Fcons id k' ftl')
  end.

Definition trans_var(te: typenv)(var: ident*kind*singleclock) : res (ident*kind*singleclock) :=
  match var with 
  | (id, k, ck) => 
    do k' <- trans_kind te k;
    OK (id, k', ck)
  end.

Definition trans_varblk(te: typenv)(vars: varBlk) : res varBlk :=
  match vars with 
  | VarList vars =>
    do vars' <- mmap (trans_var te) vars;
    OK (VarList vars')
  | NOVARBLK => OK NOVARBLK
  end.

Definition trans_bodyblk(te: typenv)(b: bodyBlk) : res (bodyBlk) :=
  match b with
  | BodyBlk vas eqs =>
    do vas' <- trans_varblk te vas;
    OK (BodyBlk vas' eqs)
  end.

Definition constblkof(nd: nodeBlk): list constStmt :=
  match nd with
  | ConstBlk cl => cl
  | _ => nil
  end.

Definition typeblkof(nd: nodeBlk): list typeStmt :=
  match nd with
  | TypeBlk tys => tys
  | _ => nil
  end.

Definition trans_conststmt(te: typenv)(cs: constStmt): res constStmt :=
  match cs with
  | ConstStmt id k v =>
    do k' <- trans_kind te k;
    OK (ConstStmt id k' v)
  end.

Definition trans_nodeblk(te: typenv)(nd: nodeBlk) : res (list nodeBlk) :=
  match nd with
  | FuncBlk ft id (ParamBlk ps) (ReturnBlk rs) body =>
    do ps' <- mmap (trans_var te) ps;
    do rs' <- mmap (trans_var te) rs;
    do body' <- trans_bodyblk te body;
    OK (FuncBlk ft id (ParamBlk ps') (ReturnBlk rs') body' :: nil)
  | _ => OK nil
  end.

Fixpoint trans_nodeblks(te: typenv)(nds: list nodeBlk) : res (list nodeBlk) :=
  match nds with
  | nil => OK nil
  | nd :: ndl =>
    do l1 <- trans_nodeblk te nd;
    do l2 <- trans_nodeblks te ndl;
    OK (l1 ++ l2)
  end.

End TRANSLATION.


Section TOPOTYPES.

Fixpoint typenamesof(t: kind) : list AST.ident :=
  match t with
  | Array ty _ => typenamesof ty 
  | Struct fld => typenamesof_fields fld
  | TypeDef id => (key id) :: nil     
  | _ => nil
  end

with typenamesof_fields(fld: fieldlist) : list AST.ident :=
  match fld with
  | Tree.Fnil => nil
  | Tree.Fcons _ ty ftl => typenamesof ty ++ typenamesof_fields ftl
  end.

Local Open Scope string_scope.

Definition nullstr : str := "".

Definition nullid : ident := {| name := nullstr; key := xH |}.

Definition nullkind := TypeStmt nullid (AtomType Int).

Definition nameof(ts: typeStmt) : AST.ident :=
  match ts with 
  | TypeStmt id k => key id
  end.

Definition kindof(ts: typeStmt) : kind :=
  match ts with 
  | TypeStmt id k => k
  end.

Definition deps_of_type (types: list typeStmt)(n: nat): depend :=
  let ity := nth n types nullkind in
  mkdepend (nameof ity :: nil) (typenamesof (kindof ity)) n.

Definition deps_of_types (types: list typeStmt): list depend :=
  map (deps_of_type types) (seq O (List.length types)).

Definition toposort_types (types: list typeStmt) : res (list typeStmt):=
  let depl := deps_of_types types in 
  do depl' <- toposort_deps (List.length depl) depl; 
  let ids := map seqn depl' in 
  OK (map (fun id => nth id types nullkind) ids).

End TOPOTYPES. 

Fixpoint register_typeblock(l: list typeStmt)(te: typenv) : res typenv :=
  match l with
  | nil => OK te
  | TypeStmt id k :: tl =>
    do k' <- trans_kind te k;
    register_typeblock tl (te ++ (TypeStmt id k') :: nil)
  end. 

Definition trans_program(p: program) : res program :=
  match p with
  | Program blk =>
    let tsl := flat_map typeblkof blk in
    do tsl' <- toposort_types tsl;
    do te <- register_typeblock tsl' nil;
    do consts' <- mmap (trans_conststmt te) (flat_map constblkof blk);
    do nds <- trans_nodeblks te blk;
    OK (Program (TypeBlk te :: ConstBlk consts' :: nds))
  end.
  
   


 

    
