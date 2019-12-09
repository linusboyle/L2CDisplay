Require Import AST.
Require Import Cltypes.
Require Import Errors.
Require Import Ident.
Require Import Coqlib.
Require Import Integers.
Require Import String.

Parameter int_of_str: ident -> int.

(*simplified xml formalization*)
Inductive GTree : Type :=
  | GNode : ident -> treeList -> list attribute -> GTree
with attribute : Type :=
  | AttrVal : ident -> ident -> attribute
with treeList :=
  | GNil : treeList
  | GCons : GTree -> treeList -> treeList.

Record Widget : Type := mkwidget {
  wgt_name : ident;
  wgt_sub_num : nat;
  wgt_statics : list ident;
  wgt_params : list ident;
  wgt_events : list ident
}.

Record DisplayA : Type := mkdisplaya {
  widgets : list Widget;
  displays : list GTree
}.

Local Open Scope error_monad_scope.

Fixpoint find_attr (attrs : list attribute) (name : ident) : res ident :=
  match attrs with
  | nil => Error ((MSG "Attribute ") :: (CTX name) :: (MSG " not found") :: nil)
  | (AttrVal an av) :: t => if peq name an then OK av
                            else find_attr t name
  end.

Definition parse_wgt_itf (subnode : GTree) (wid : Widget) : res Widget :=
    match subnode with
    | GNode name subnodes attrs =>
        do itf_name <- find_attr attrs (name_xml_attr tt);
        if peq name (param_xml_ele tt) then
          OK (mkwidget wid.(wgt_name) wid.(wgt_sub_num) wid.(wgt_statics) (itf_name :: wid.(wgt_params)) wid.(wgt_events))
        else if peq name (static_xml_ele tt) then
          OK (mkwidget wid.(wgt_name) wid.(wgt_sub_num) (itf_name :: wid.(wgt_statics)) wid.(wgt_params) wid.(wgt_events))
        else if peq name (event_xml_ele tt) then
          OK (mkwidget wid.(wgt_name) wid.(wgt_sub_num) wid.(wgt_statics) wid.(wgt_params) (itf_name :: wid.(wgt_events)))
        else Error (MSG "unrecognized widget interface " :: CTX name :: nil)
    end.

Fixpoint parse_wgt_itfs (subnodes : treeList) (acc : Widget) : res Widget :=
  match subnodes with
  | GNil => OK acc
  | GCons hd tl => 
    do hw <- parse_wgt_itf hd acc;
    parse_wgt_itfs tl hw
  end.

Definition parse_widget (subnodes : treeList) (attrs : list attribute) : res Widget :=
  do subw <- find_attr attrs (subw_xml_attr tt);
  do name <- find_attr attrs (name_xml_attr tt);
  let sub_num := Z.to_nat (Int.unsigned (int_of_str subw)) in
  let basew := mkwidget name sub_num nil nil nil in
  parse_wgt_itfs subnodes basew.

Fixpoint sub_ele_len (t : treeList) : nat :=
  match t with
  | GNil => O
  | GCons hd tl => S (sub_ele_len tl)
  end.

Definition parse_display (name : ident) (subnodes : treeList) (attrs : list attribute) : res GTree :=
  match subnodes with
  | GCons top GNil =>
      OK top
  | _ => Error (msg "Elements of display is not wrong!")
  end.

Definition parse_entity (ent : GTree) (acc : DisplayA) : res DisplayA :=
  match ent with
  | GNode name subnodes attrs =>
      if peq name (widget_xml_ele tt) then
        do wgt <- parse_widget subnodes attrs;
        OK (mkdisplaya (wgt :: acc.(widgets)) acc.(displays))
      else if peq name (gui_xml_ele tt) then
        do dis <- parse_display name subnodes attrs;
        OK (mkdisplaya acc.(widgets) (dis :: acc.(displays)))
      else Error ((MSG "unrecognized entity:") :: (CTX name) :: nil)
  end.

Fixpoint parse_entities (entities : treeList) (acc : DisplayA) : res DisplayA :=
  match entities with
  | GNil => OK acc
  | GCons hd tl =>
      do hw <- parse_entity hd acc;
      parse_entities tl hw
  end.

Definition parse_gtree (gm : GTree) : res DisplayA :=
  match gm with
  | GNode name entities attrs =>
      if peq name (toplevel_xml_ele tt) then
        let base := mkdisplaya nil nil in
        parse_entities entities base 
      else Error (msg "toplevel element is not correct")
  end.
