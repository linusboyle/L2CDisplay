Require Import AST.
Require Import Coqlib.
Require Import Ctypes.
Require Import Errors.
Require Import DisplayS.
Require Import Maps.
Require Import Clight.
Require ClightGen.
Require DisplaySGen.

Definition tempvar_name (nd sl : ident) := Lident.intern_string (String.append (String.append (Lident.extern_atom nd) "_" ) (Lident.extern_atom sl)).

Definition gen_tempvar (nd : ident) (acc : list (ident * type)) (arg : ident * Cltypes.type) :=
  let (sl, ty) := arg in
  let ty' := ClightGen.trans_type ty in
  (tempvar_name nd sl, ty') :: acc.

Definition gen_main_stmt (main : ident) (fe : expr) (stmt : statement) (arg : ident * Cltypes.type) :=
  let (sl, ty) := arg in
  let ty' := ClightGen.trans_type ty in
  let field_expr := Efield fe sl ty' in
  let rval := Evar (tempvar_name main sl) ty' in
  Ssequence stmt (Sassign field_expr rval).

Definition gen_main_stmts (main : ident) (st : type) (args : list (ident * Cltypes.type)) : statement :=
  let deref_expr := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
  let in_struct := Lident.acg_inc_name main in
  let field_expr := Efield deref_expr in_struct (Tstruct in_struct Fnil noattr) in
  List.fold_left (gen_main_stmt main field_expr) args Sskip.

Definition gen_tempvars_nd (main : ident) (st : type) (acc : list (ident * type) * statement) (ele : ident * LustreS.node) :=
  let (nm, nd) := ele in
  let args := Lustre.nd_args nd in
  let stmt := snd acc in
  let stmt' := 
    if peq main nm then Ssequence stmt (gen_main_stmts main st args)
    else stmt
  in
  (*if peq main nm then (tempvar_name nm Lident.INSTRUCT, Tstruct (Lident.acg_inc_name main) Fnil noattr) :: acc*)
  (List.fold_left (gen_tempvar nm) args (fst acc), stmt').

Definition gen_tempvars (ne : DisplayT.nodeenv) (main : ident) (st : type) : list (ident * type) * statement :=
  let eles := PTree.elements ne in
  List.fold_left (gen_tempvars_nd main st) eles (nil, Sskip).

Definition extenv := PTree.t fundef.
Definition empty_extenv := PTree.empty fundef.

Definition update_in_func_name (sn wty : ident) :=
  Lident.intern_string (String.append (Lident.extern_atom wty) (String.append "_update_and_get_" (Lident.extern_atom sn))).

Definition update_in_func_tylist (wty : ident) := Tcons (DisplaySGen.get_widget_type wty) Tnil.

Definition update_in_func (fn wty : ident) (ty : type) : fundef :=
  let tylist := update_in_func_tylist wty in
  External (EF_external fn DisplaySGen.null_signature) tylist ty cc_default.

Definition get_field_expr (w : widget) (st : type) :=
  let deref_expr := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
  let wty := DisplaySGen.get_widget_type w.(wty) in
  Efield deref_expr w.(wid) wty.

Definition gen_assign_in (st : type) (sl : slotS) (w : widget) (sp : statement * extenv) :=
  let (stmt, te) := sp in
  let wdty := wty w in
  let func_name := update_in_func_name sl.(nm) wdty in
  let te' := match te ! func_name with
            | None =>
                let fc := update_in_func func_name wdty sl.(ty) in
                PTree.set func_name fc te
            | Some _ => te
            end
  in
  let lval := tempvar_name sl.(nd) sl.(pa) in
  let func_exp := Evar func_name (Tfunction (update_in_func_tylist wdty) sl.(ty) cc_default) in
  let ref_exp := (get_field_expr w st) :: nil in
  let stmt' := Scall (Some lval) func_exp ref_exp in
  (Ssequence stmt stmt', te').

Definition gen_stmt_in (st : type) (w : widget) (sp : statement * extenv) :=
  let sls := slin w in
  List.fold_left (fun sp sl => gen_assign_in st sl w sp) sls sp .

Definition gen_stmts_in (st : type) (wgts : list widget) (te : extenv) := List.fold_left (fun sp wgt => gen_stmt_in st wgt sp) wgts (Sskip, te).

Fixpoint gen_nd_argexpr (nm : ident) (args : list (ident * Cltypes.type)) (acc : typelist * list expr) : typelist * list expr :=
  match args with
  | nil => acc
  | (nd, ty) :: tl =>
      let ty' := ClightGen.trans_type ty in
      let (tyl, exps) := acc in
      let var_exp := Evar (tempvar_name nm nd) ty' in
      gen_nd_argexpr nm tl (Tcons ty' tyl, var_exp :: exps)
  end.

Definition gen_main_argexpr (main :ident) (st : type) (nd : LustreS.node) (acc : typelist * list expr) : typelist * list expr :=
  let in_name := Lident.acg_inc_name main in
  let param_type := (Tpointer (Tstruct in_name Fnil noattr) noattr) in 
  let tyl := Tcons param_type (fst acc) in
  let deref_expr := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
  let field_expr := Efield deref_expr in_name (Tstruct in_name Fnil noattr) in
  let ref_expr := Eaddrof field_expr param_type in
  (tyl, ref_expr :: snd acc).

Definition gen_outexp (nm : ident) (st : type) : type * expr :=
  let ty := Tstruct nm Fnil noattr in
  let rty := Tpointer ty noattr in
  let out_name := Lident.acg_outc_name nm in
  let deref_expr := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
  let field_expr := Efield deref_expr out_name ty in
  let ref_expr := Eaddrof field_expr rty in
  (rty, ref_expr).

Definition gen_stmt_call (main : ident) (st : type) (stmt : statement) (ele : ident * LustreS.node) : statement :=
  let (nm, nd) := ele in
  let (rty, out_exp) := gen_outexp nm st in
  let (tylist, args) :=
    if peq nm main then gen_main_argexpr main st nd (Tcons rty Tnil, out_exp :: nil)
    else gen_nd_argexpr nm nd.(Lustre.nd_args) (Tcons rty Tnil, out_exp :: nil)
  in
  let func_exp := Evar nm (Tfunction tylist Tvoid cc_default) in
  let call_stmt := Scall None func_exp args in
  Ssequence stmt call_stmt.

Definition gen_stmts_call (ne : DisplayT.nodeenv) (main : ident) (st : type) :=
  let eles := PTree.elements ne in
  List.fold_left (gen_stmt_call main st) eles Sskip.

Definition update_func_name := Lident.intern_string "update_display_ctx".

Definition update_out_func_name (sn wty : ident) :=
  Lident.intern_string (String.append (Lident.extern_atom wty) (String.append "_update_and_put_" (Lident.extern_atom sn))).

Definition update_out_func_tylist (wty : ident) (sty : type) := Tcons (DisplaySGen.get_widget_type wty) (Tcons sty Tnil).

Definition update_out_func (fn wty: ident) (ty : type) :=
  External (EF_external fn DisplaySGen.null_signature) (update_out_func_tylist wty ty) Tvoid cc_default.

Definition gen_out_fieldexpr (st : type) (sl : slotS) :=
  let deref_expr := Ederef (Evar Lident.INSTRUCT (Tpointer st noattr)) st in
  let out_name := Lident.acg_outc_name sl.(nd) in
  let field_expr := Efield deref_expr out_name (Tstruct out_name Fnil noattr) in
  Efield field_expr sl.(pa) sl.(ty).

Definition gen_assign_out (st : type) (wgt : widget) (sp : statement * extenv) (sl : slotS) : statement * extenv :=
  let (stmt, te) := sp in
  let wdty := wty wgt in
  let func_name := update_out_func_name sl.(nm) wdty in
  let te' := match te ! func_name with
            | None =>
                let fc := update_out_func func_name wdty sl.(ty) in
                PTree.set func_name fc te
            | Some _ => te
            end
  in
  let lval := tempvar_name sl.(nd) sl.(pa) in
  let func_exp := Evar func_name (Tfunction (update_out_func_tylist wdty sl.(ty)) Tvoid cc_default) in
  let ref_exp := (get_field_expr wgt st) :: (gen_out_fieldexpr st sl) :: nil in
  let stmt' := Scall None func_exp ref_exp in
  (Ssequence stmt stmt', te').

Definition gen_const_stmt (st : type) (wgt : widget) (sp : statement * extenv) (const : ident * ident * type) : statement * extenv :=
  let (stmt, te) := sp in
  let (sl, id) := fst const in
  let ty := snd const in
  let wty := wgt.(wty) in
  let wid := wgt.(wid) in
  let func_name := update_out_func_name sl wty in
  let te' := match te ! func_name with
            | None =>
                let fc := update_out_func func_name wty ty in
                PTree.set func_name fc te
            | Some _ => te
            end
  in
  let params := (get_field_expr wgt st) :: (Evar id ty) :: nil in
  let func_exp := Evar func_name (Tfunction (update_out_func_tylist wty ty) Tvoid cc_default) in
  let stmt' := Scall None func_exp params in
  (Ssequence stmt stmt', te').

Definition gen_stmt_out (st : type) (sp : statement * extenv) (wgt : widget) : statement * extenv :=
  let sls := wgt.(slout) in
  let sp_out := List.fold_left (gen_assign_out st wgt) sls sp in
  let consts := wgt.(slconst) in
  List.fold_left (gen_const_stmt st wgt) consts sp_out.

Definition gen_stmts_out (st : type) (wgts : list widget) (te : extenv) :=
  List.fold_left (fun sp wgt => gen_stmt_out st sp wgt) wgts (Sskip, te).

Definition trans_model (m : modelS) : res modelS' :=
  let ne := node_valS m in
  let st := structS m in
  let main := node_mainS m in
  let (vars, stmt_assign) := gen_tempvars ne main st in
  let wgts := widgetS m in
  let (stmt_in, ex0) := gen_stmts_in st wgts empty_extenv in
  let stmt_ndcall := gen_stmts_call ne main st in
  let (stmt_out, ex1) := gen_stmts_out st wgts ex0 in
  let stmt := Ssequence (Ssequence (Ssequence stmt_in stmt_assign) stmt_ndcall) stmt_out in
  let params := (Lident.INSTRUCT, Tpointer st noattr) :: nil in
  let update_func := mkfunction Tvoid cc_default params vars nil stmt in
  OK (mkmodelS' st m.(createFuncS) (update_func_name, update_func) (m.(external_funcS) ++ PTree.elements ex1) m.(const_valS)).
