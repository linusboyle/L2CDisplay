Require Import AST.
Require Import Cltypes.
Require Import DisplayT.
Require Import Maps.
Require Import Coqlib.
Require Import LustreSGen.
Require Import Errors.

Definition seq := PTree.t positive.
Definition empty_seq := PTree.empty positive.

Definition get_widget_type (w : ident) : type :=
  let wn := Lident.extern_atom w in
  let tn := String.append "handler_" wn in
  Tpointer (Tstruct (Lident.intern_string tn) Fnil). (* no field needed *)

Definition get_field_name (w : ident) (num : positive) :=
  Lident.intern_string (String.append (Lident.extern_atom w) (Lident.string_of_positive num)).

Definition check_seq (wn: ident) (se : seq) :=
  match se ! wn with
  | None => PTree.set wn xH se
  | Some _ => se
  end.

Fixpoint gen_seq (d : displayT) (se : seq) : seq :=
  match d with
  | TNode wn dl sl =>
      let se0 := check_seq wn se in
      gen_seqs dl se0
  end
with gen_seqs (dl : displayList) (se : seq) :=
  match dl with
  | TNil => se
  | TCons d dl' =>
      let se0 := gen_seq d se in
      gen_seqs dl' se0
  end.

Fixpoint fl_append (f1 f2 : fieldlist)  :=
  match f1 with
  | Fnil => f2
  | Fcons id ty rem =>
      let f' := fl_append rem f2 in
      Fcons id ty f'
  end.

Local Open Scope error_monad_scope.

Definition trans_slot (sl : slot) :=
  match sl with
  | TConst _ _ => sl
  | TRefin sn nd pa ty =>
      (*change the node name to field name, see gen_ndstructs below for why*)
      let iname := Lident.acg_inc_name nd in
      TRefin sn iname pa ty
  | TRefout sn nd pa ty =>
      let oname := Lident.acg_outc_name nd in
      TRefout sn oname pa ty
  end.

Fixpoint gen_field (d : displayT) (se: seq) : res (displayT * seq * fieldlist) :=
  match d with
  | TNode wn dl sl =>
      let tn := get_widget_type wn in
      do (dl0, se0, fl0) <- gen_fields dl se;
      match se0 ! wn with
      | None => Error (msg "failed to generate field")
      | Some num => 
          let fn := get_field_name wn num in
          let fl := Fcons fn tn fl0 in
          let d' := TNode fn dl0 (List.map trans_slot sl) in
          let se1 := PTree.set wn (Pos.succ num) se0 in
          OK (d', se1, fl)
      end
  end
with gen_fields (dl : displayList) (se : seq) : res (displayList * seq * fieldlist) :=
  match dl with
  | TNil => OK (dl, se, Fnil)
  | TCons d dl0 =>
      do (d', se0, fl0) <- gen_field d se;
      do (dl1, se1, fl1) <- gen_fields dl0 se0;
      let fl' := fl_append fl0 fl1 in
      let dl' := TCons d' dl1 in
      OK (dl', se1, fl')
  end.

Definition mkstruct (nm : ident) := Tstruct nm Fnil.

Definition gen_ndstructs (nid : list ident) : fieldlist :=
  List.fold_left 
  (fun fd id => 
    let in_name := Lident.acg_inc_name id in
    let out_name := Lident.acg_outc_name id in
    Fcons in_name (mkstruct in_name) (Fcons out_name (mkstruct out_name) fd)
  )
  nid Fnil.

Definition generate_struct (m0 : modelT) : res modelT' :=
  let ce := const_envT m0 in
  let nid := List.map fst (PTree.elements (node_envT m0)) in
  let sfds := gen_ndstructs nid in
  let se := gen_seq (display m0) empty_seq in
  do (dis, se0, fds) <- gen_field (display m0) se;
  OK (mkmodelT' dis ce nid (Tstruct xH (fl_append sfds fds))).
