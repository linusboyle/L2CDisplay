Require Import AST.
Require Import Coqlib.
Require Import Maps.
Require Import DisplayW.

Record widgetInstance : Type := mkinstance {
  wgt_name : ident; (* widget name *)
  wgt_id : option ident; (* a human-readable id *)
  wgt_num : positive; (* a program-unique id *)
  wgt_statics : list (ident * ident) (* static parameters *)
}.

Inductive markUp : Type :=
  | GraphicsHierarchy : widgetInstance -> instanceTree -> markUp
with instanceTree : Type :=
  | INil : instanceTree
  | ICons : markUp -> instanceTree -> instanceTree.

(* distribute unique widget number *)
Fixpoint generate_num (ne : positive) (m0 : markUp) : positive * markUp :=
  match m0 with
  | GraphicsHierarchy wgt subl =>
      let (ne', subl') := generate_nums ne subl in
      let wgt' := mkinstance wgt.(wgt_name) wgt.(wgt_id) ne' wgt.(wgt_statics) in
      (Pos.succ ne', GraphicsHierarchy wgt' subl')
  end
with generate_nums (ne : positive) (il : instanceTree) : positive * instanceTree :=
  match il with
  | INil => (ne, INil)
  | ICons h t =>
      let (ne0, h') := generate_num ne h in
      let (ne1, t') := generate_nums ne0 t in
      (ne1, ICons h' t')
  end.

Definition trans_markup (m: markUp) :=
  snd (generate_num xH m).

Set Implicit Arguments.

Section META_INFO.

Variable T C : Type.

Record general_info : Type := mkinfo {
  mid : ident;
  mty : T;
  mclk : C
}.

End META_INFO.

Section META.

Variable G : Type.
Definition general_megaenv : Type := list ((ident * ident) * G).

Definition add  (key : ident * ident) (id : G) (me : general_megaenv) : general_megaenv :=
  (key, id) :: me.

Definition eqb_mega (op1 : ident * ident) (op2 : ident * ident) : bool :=
  let (kw, kf) := op1 in
  let (kw', kf') := op1 in
  andb (peq kw kw') (peq kf kf').

Fixpoint find (key : ident * ident) (me : general_megaenv) : option G :=
  match me with
  | nil => None
  | (key', va) :: t =>
    if eqb_mega key key' then Some va
    else find key t
  end.

End META. 

Definition meta_infoW := general_info typeL Lustre.clock.
Definition megaenvW : Type := general_megaenv meta_infoW.

Record extinfoW : Type := mkext {
  wgt_itfW : widgetenv;  
  wgt_relationW : megaenvW (* here, relation means the dependency between gui events/parameters and clight variables *)
}. 
