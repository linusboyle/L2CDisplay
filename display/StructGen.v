Require Import AST.
Require Import Cltypes.
Require Import Maps.
Require Import Coqlib.
Require Import LustreSGen.
Require Import Errors.
Require Import DisplayT.

Definition seq := PTree.t positive.
Definition empty_seq := PTree.empty positive.

Definition wchecker := PTree.t nat.
Definition empty_wchecker := PTree.empty nat.

Definition check (wn : ident) (len : nat) (wc : wchecker) : res (wchecker) :=
  match wc ! wn with
  | None => OK (PTree.set wn len wc)
  | Some len' => if beq_nat len' len then OK wc
                                 else Error (MSG "widget " :: CTX wn :: MSG " has different subwidgets list!" :: nil)
  end.

Record generator : Type := mkgenerator {
  sequence : seq;
  checker : wchecker
}.

Definition mkstruct (nm : ident) := Tstruct nm Fnil.

Definition get_widget_type (w : ident) : type :=
  let wn := Lident.extern_atom w in
  let tn := String.append "handler_" wn in
  Tpointer (mkstruct (Lident.intern_string tn)). (* no field needed *)

Definition get_field_name (w : ident) (num : positive) :=
  Lident.intern_string (String.append (Lident.extern_atom w) (Lident.string_of_positive num)).

Fixpoint fl_append (f1 f2 : fieldlist) :=
  match f1 with
  | Fnil => f2
  | Fcons id ty rem =>
      let f' := fl_append rem f2 in
      Fcons id ty f'
  end.

Local Open Scope error_monad_scope.

Fixpoint gen_field (d : displayT) (ge : generator) : res (displayT' * generator * fieldlist) :=
  match d with
  | TNode wn dl sl =>
      do (dl0, ge0, fl0) <- gen_fields dl ge;
      let se0 := sequence ge0 in
      let num := match se0 ! wn with
                | None => xH
                | Some num => num
                end in
      let fn := get_field_name wn num in
      let tn := get_widget_type wn in
      let fl := Fcons fn tn fl0 in
      let d' := TNode (wn, fn) dl0 sl in
      let se1 := PTree.set wn (Pos.succ num) se0 in
      do wc1 <- check wn (length dl) (checker ge0);
      OK (d', mkgenerator se1 wc1, fl)
      end
with gen_fields (dl : displayListT) (ge : generator) : res (displayListT' * generator * fieldlist) :=
  match dl with
  | TNil => OK (TNil, ge, Fnil)
  | TCons d dl0 =>
      do (d', ge0, fl0) <- gen_field d ge;
      do (dl1, ge1, fl1) <- gen_fields dl0 ge0;
      let fl' := fl_append fl0 fl1 in
      let dl' := TCons d' dl1 in
      OK (dl', ge1, fl')
  end.

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
  let ge := mkgenerator empty_seq empty_wchecker in
  do (dis, se0, fds) <- gen_field (display m0) ge;
  OK (mkmodelT' dis ce nid (Tstruct xH (fl_append sfds fds))).
