Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Display.
Require Import LustreS.
Require Import Cltypes.
Require Import Errors.

Definition nodeenv := PTree.t (LustreS.node).
Definition empty_nodeenv := PTree.empty (LustreS.node).

Definition err_nd_notfound (ndname : ident) : res unit :=
  Error ((MSG "Node ") :: (CTX ndname) :: (MSG " not found" :: nil)).

Definition err_sl_notfound (slname : ident) : res unit :=
  Error ((MSG "Paramemter ") :: (CTX slname) :: (MSG " not found" :: nil)).

Definition err_ty_incompatible : res unit :=
  Error (msg "Type not compatible").

Definition add_node (ne: nodeenv) (nd : ident * LustreS.node) :=
  PTree.set (fst nd) (snd nd) ne.

Fixpoint register_node (ne: nodeenv) (nodes : list (ident * LustreS.node)) :=
  match nodes with
  | nil => ne
  | nhd :: ntl =>
      let ne1 := add_node ne nhd in
      register_node ne1 ntl
  end.

(*NOTE: wrong impl*)
Fixpoint check_type (source target: type) : res unit :=
  match (source, target) with 
  | (Tarray _ t1 sz1, Tarray _ t2 sz2) => 
      check_type t1 t2
  | (Tint _ _, Tint _ _) => OK tt
  | (Tpointer t1, Tarray _ t2 sz2) => check_type t1 t2
  | (Tarray _ t1 sz1, Tpointer t2) => check_type t1 t2
  | (_, _) => if type_eq source target then OK tt
              else err_ty_incompatible
  end.

Fixpoint check_slot (varlist: list(ident*type)) (ty: type) (slname: ident) : res unit :=
  match varlist with 
  | nil => err_sl_notfound slname
  | (vi, vt) :: tl => if peq slname vi then check_type vt ty
                      else check_slot tl ty slname
  end.

Definition slotcheck_in { A : type } (ne: nodeenv) (inpt: InputSlot A) : res unit :=
  match inpt with 
  | None => OK tt
  | Some (NRconstruct ndname slname) => 
    match ne ! ndname with
    | None => err_nd_notfound ndname
    | Some nd => 
        let args := Lustre.nd_args nd in
        check_slot args A slname
    end
  end.

Definition slotcheck_out { A : type } (ne: nodeenv) (output: OutputSlot A) : res unit :=
  match output with
  | STconst _ => OK tt
  | STref (NRconstruct ndname slname) =>
    match ne ! ndname with
    | None => err_nd_notfound ndname
    | Some nd =>
        let rets := Lustre.nd_rets nd in
        check_slot rets A slname
    end
  end.

Local Open Scope error_monad_scope.

Fixpoint model_analysis (model: display) (ne: nodeenv) : res unit :=
  match model with
  | Vstack m1 m2 | Hstack m1 m2 => 
      do t1 <- model_analysis m1 ne;
      model_analysis m2 ne
  | Button text click => 
      do t1 <- slotcheck_out ne text;
      slotcheck_in ne click
  | Label text => slotcheck_out ne text
  | Input text submit => 
      do t1 <- slotcheck_in ne text;
      slotcheck_in ne submit
  end.

Definition analysis (model: display) (p : LustreS.program) : res unit :=
  let ne := register_node empty_nodeenv (Lustre.node_block p) in
  model_analysis model ne.
