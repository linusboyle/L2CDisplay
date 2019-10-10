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
Require Import Integers.
Require Import Floats.
Require Import Zwf.
Require Import Maps.
Require Import Memory.
Require Import Globalenvs.
Require Import Ctypes.
Require Import Cltypes.
Require Import ExtraList.
Require Import Streams.
Require Import Peano.
Require Import Lident.
Require Import Ltypes.
Require Import Lvalues.
Require Import Lustre.
Require Import Lenv.

Set Implicit Arguments.

Section GLOBAL_ENV.

(** Global environment. *)

Definition globalenv:= PTree.t (list init_data).

Definition empty_globalenv := PTree.empty (list init_data).

Definition find_init_data(gv: globalenv)(id: init_data): option init_datas:=
  match id with
  | Init_addrof symbol _ => gv ! symbol
  | _ => Some (id :: nil) 
  end.

Fixpoint find_init_datas(gv: globalenv)(idl: init_datas): option init_datas :=
  match idl with
  | nil => Some nil
  | id :: idl' =>
      match find_init_data gv id with
      | None => None
      | Some idl1 => 
        match find_init_datas gv idl' with
        | None => None
        | Some idl2 => Some (idl1 ++ idl2)
        end
      end
  end.

Definition alloc_global(gc:locenv)(gv: globalenv)(idl: (ident * globvar type)): option (locenv*globalenv) :=
  match idl with
  | (id, (mkglobvar ty init _ _)) =>
    match find_init_datas gv init with
    | None => None
    | Some init' =>
      let sz := Genv.init_data_list_size init' in 
      match store_zeros (alloc sz) sz with
      | None => None
      | Some m1 =>
        match store_init_datas m1 0 init' with
        | None => None
        | Some m2 => Some (PTree.set id (m2,ty) gc, PTree.set id init' gv)
        end
      end
    end
  end.

Fixpoint alloc_globals(gc: locenv)(gv: globalenv)(gl: list (ident * globvar type)): option (locenv*globalenv) :=
  match gl with
  | nil => Some (gc,gv)
  | idl :: gl' =>
      match alloc_global gc gv idl with
      | None => None
      | Some (gc', gv') => alloc_globals gc' gv' gl'
      end
  end.

Definition init_genvc(gl: list (ident * globvar type)): option (locenv*globalenv) :=
  alloc_globals empty_locenv empty_globalenv gl.

Lemma alloc_globals_app:
  forall l1 l2 gc gc1 gc2 gv gv1 gv2,
  alloc_globals gc gv l1 = Some (gc1, gv1) ->
  alloc_globals gc1 gv1 l2 = Some (gc2, gv2) ->
  alloc_globals gc gv (l1++l2) = Some (gc2, gv2).
Proof.
  induction l1; simpl; intros.
  congruence.
  destruct (alloc_global gc gv a) eqn:?; try congruence.
  destruct p. eapply IHl1; eauto.
Qed.

Lemma alloc_globals_notin_eq_right:
  forall id l gc gc' gv gv',
  alloc_globals gc gv l = Some (gc', gv')-> 
  ~ In id (List.map (@fst ident (globvar type)) l) ->
  gv' ! id =gv ! id.
Proof.
  induction l; simpl; intros.
  +inv H. auto.
  +destruct (alloc_global gc gv a) eqn:?; try congruence.
   destruct p as [gc0 gv0].
   rewrite IHl with gc0 gc' gv0 gv'; eauto.
   unfold alloc_global in Heqo. destruct a.
   destruct g.
   destruct (find_init_datas _ _) eqn:?; try congruence.
   destruct (store_zeros _ _) eqn:?; try congruence.
   destruct (store_init_datas _ _ _) eqn:?; inv Heqo.
   rewrite PTree.gso; auto.
Qed.

Variable S: Type. 

Variable p: general_program (general_node S).
Variable gc: locenv.


Variable alloc_node: general_program (general_node S) -> env -> ident*general_node S -> Prop.

Inductive initial_state(main: ident*general_node S): env -> Prop := 
  | initial_state_node: forall gv e, 
      init_genvc (const_block p) = Some (gc,gv) ->
      find_funct (node_block p) p.(node_main) = Some main -> 
      alloc_node p e main ->
      initial_state main e.

End GLOBAL_ENV.

