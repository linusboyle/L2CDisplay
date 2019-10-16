Require Import Coqlib.
Require Import Maps.
Require Import AST.
Require Import Display.
Require Import LustreS.

Definition nodeenv := PTree.t (LustreS.node).
Definition empty_nodeenv := PTree.empty (LustreS.node).

Definition add_node (ne: nodeenv) (nd : ident * LustreS.node) :=
  PTree.set (fst nd) (snd nd) ne.

Fixpoint register_node (ne: nodeenv) (nodes : list (ident * LustreS.node)) :=
  match nodes with
  | nil => ne
  | nhd :: ntl =>
      let ne1 := add_node ne nhd in
      register_node ne1 ntl
  end.

Definition check_node (ne: nodeenv) (ndname: ident) : bool :=
    match ne ! ndname with
    | None => false
    | Some _ => true
    end.

Definition slotcheck_in { A : Type } (ne: nodeenv) (inpt: InputSlot A) : bool :=
  match inpt with 
  | None => true
  | Some (NRconstruct ndname slname) => 
    check_node ne ndname
  end.

Definition slotcheck_out { A : Type } (ne: nodeenv) (output: OutputSlot A) : bool :=
  match output with
  | STconst _ => true
  | STref (NRconstruct ndname slname) =>
    check_node ne ndname
  end.

Fixpoint model_analysis (model: display) (ne: nodeenv) : bool :=
  match model with
  | Vstack m1 m2 | Hstack m1 m2 => andb (model_analysis m1 ne) (model_analysis m2 ne)
  | Button text click => andb (slotcheck_out ne text) (slotcheck_in ne click)
  | Label text => slotcheck_out ne text
  | Input text submit => andb (slotcheck_in ne text) (slotcheck_in ne submit)
  end.

Definition analysis (model: display) (p : LustreS.program) : bool :=
  let ne := register_node empty_nodeenv (Lustre.node_block p) in
  model_analysis model ne.
