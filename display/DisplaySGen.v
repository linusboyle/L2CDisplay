Require Import AST.
Require Import Clight.
Require Import Coqlib.
Require Import Ctypes.
Require Import DisplayS.
Require Import DisplayT.
Require Import Errors.
Require Import Maps.
Require ClightGen.
Require StructGen.

Record counter : Type := mkcounter {
  sin : list slotS;
  sout : list slotS;
  scons : list (ident * ident * type)
}.

Definition extenv := PTree.t (ident * fundef).
Definition empty_extenv := PTree.empty (ident * fundef).

Definition trans_slot_accum (co : counter) (s : slot) : counter :=
  match s with
  | TConst nm vn ty => mkcounter (sin co) (sout co) ((nm, vn, (ClightGen.trans_type ty)) :: (scons co))
  | TRefin nm nd pa ty => mkcounter (mkslotS nm nd pa (ClightGen.trans_type ty) :: sin co) (sout co) (scons co)
  | TRefout nm nd pa ty => mkcounter (sin co) (mkslotS nm nd pa (ClightGen.trans_type ty) :: sout co) (scons co)
  end.

Fixpoint to_widget (d : displayT') (ret : list widget) : list widget :=
  match d with
  | TNode (wn, id) sub sl =>
      let co := List.fold_left trans_slot_accum sl (mkcounter nil nil nil) in
      let w := mkwidget wn id (sin co) (sout co) (scons co) in 
      to_widgets sub (w :: ret)
  end
with to_widgets (ds : displayListT') (ret : list widget) : list widget :=
  match ds with
  | TNil => ret
  | TCons d0 ds' => 
      let ws0 := to_widgets ds' ret in
      to_widget d0 ws0
  end.

Definition reset_call (nd : ident) (st : type) : statement :=
  let osty := Tstruct (Lident.acg_outc_name nd) Fnil noattr in
  let cty := Tpointer osty noattr in
  let func_expr := Evar (Lident.acg_reset_name nd) (Tfunction (Tcons cty Tnil) Tvoid cc_default) in
  let ins := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
  let field_expr := Efield ins (Lident.acg_outc_name nd) osty in
  let ref_expr := Eaddrof field_expr cty in
  Scall None func_expr (ref_expr :: nil).

Definition reset_gen (nodes : list ident) (st : type) : statement :=
  List.fold_left (fun stmt nd => Ssequence (reset_call nd st) stmt) nodes Sskip.

Definition null_signature := mksignature nil None cc_default.

Local Open Scope error_monad_scope.

Fixpoint voidlist_gen (len : nat) (com : typelist) : typelist :=
  match len with
  | O => com
  | S m => voidlist_gen m (Tcons (Tpointer Tvoid noattr) com)
  end.

Definition get_widget_type (wn : ident) : type :=
  ClightGen.trans_type (StructGen.get_widget_type wn).

Definition ext_gen (wn : ident) (len : nat) : ident * typelist :=
  let fn := Lident.intern_string (String.append "create_" (Lident.extern_atom wn)) in
  let sub_list := voidlist_gen len Tnil in
  (fn, Tcons (get_widget_type wn) sub_list).

Definition get_field_expr (d : displayT') (st : type) : expr :=
  match d with
  | TNode (wn, wid) dl sl =>
    let deref_expr := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
    let wty := get_widget_type wn in
    let field_expr := Efield deref_expr wid wty in
    field_expr
  end.

Fixpoint get_field_exprs (dl : displayListT') (st : type) : list expr :=
  match dl with
  | TNil => nil
  | TCons d dl' => get_field_expr d st :: get_field_exprs dl' st
  end.

Fixpoint create_gen (d : displayT') (fe : extenv) (st : type) : res (statement * extenv) :=
  match d with
  | TNode (wn, wid) dl sl =>
      do (st0, fe0) <- create_gens dl fe st;
      let params := (get_field_expr d st) :: get_field_exprs dl st in
      do (fn, tylist) <-
        match fe0 ! wn with
        | None => OK (ext_gen wn (DisplayT.length dl))
        | Some (fn, (External _ tylist _ _)) => OK (fn, tylist)
        | _ => Error (msg "failure in create_gen()")
        end;
      let ex_func := External (EF_external fn null_signature) tylist Tvoid cc_default in 
      let func_exp := Evar fn (Tfunction tylist Tvoid cc_default) in 
      let callst := Scall None func_exp params in
      OK ((Ssequence st0 callst), PTree.set wn (fn, ex_func) fe0)
  end
with create_gens (dl : displayListT') (fe : extenv) (st : type) : res (statement * extenv) := 
  match dl with
  | TNil => OK (Sskip, fe)
  | TCons d dl' =>
      do (st0, fe0) <- create_gen d fe st;
      do (st1, fe1) <- create_gens dl' fe0 st;
      OK ((Ssequence st0 st1), fe1)
  end.

Fixpoint trans_const (cv : ident * globvar Cltypes.type) : ident * globvar type :=
  let nm := fst cv in
  let gv := snd cv in
  (nm, mkglobvar (ClightGen.trans_type gv.(gvar_info)) gv.(gvar_init) gv.(gvar_readonly) gv.(gvar_volatile)).

Definition create_func_name := Lident.intern_string "create_display_ctx".

Definition trans_model (mt : modelT') : res modelS :=
  let st := ClightGen.trans_type (structT mt) in
  let cvals := List.map trans_const (PTree.elements (const_envT' mt)) in
  let nodes := List.map fst (PTree.elements (node_envT' mt)) in
  let stmts0 := reset_gen nodes st in
  do (stmts1, exts) <- create_gen (display' mt) empty_extenv st;
  let params := (Lident.INSTRUCT, Tpointer st noattr) :: nil in
  let func := mkfunction Tvoid cc_default params nil nil (Ssequence stmts0 stmts1) in
  OK (mkmodelS (to_widget (display' mt) nil) (List.map snd (PTree.elements exts)) (create_func_name, func) cvals (node_envT' mt) (node_mainT' mt) st).
