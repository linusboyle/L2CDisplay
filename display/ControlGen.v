Require Import AST.
Require Import Coqlib.
Require Import MarkUp.
Require Import Maps.
Require Import DisplayW.
Require Import Csim.
Require Import Integers.
Require Import Cltypes.
Require Import Lident.
Require Import Lustre.
Require Import Errors.
Require Import Integers.
Require LustreVGen.
Require LustreWGenDis.

(* distribute unique instance number *)
Fixpoint generate_num_impl (ne : positive) (m0 : markUp) : positive * markUp :=
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
      let (ne0, h') := generate_num_impl ne h in
      let (ne1, t') := generate_nums ne0 t in
      (ne1, ICons h' t')
  end.

Definition generate_num (m: markUp) :=
  snd (generate_num_impl xH m).

Local Open Scope error_monad_scope.

Section WGTINFO.

Definition varsenv : Type := PTree.t (type * clock).
Definition empty_varsenv := PTree.empty (type * clock).

Definition staticenv : Type := PTree.t type.
Definition empty_staticenv := PTree.empty type.

Record widget_info : Type := mkwinfo {
  subwgt_len : option nat;
  params_info : varsenv;
  events_info : varsenv;
  statics_info : staticenv
}.

Definition wgtenv : Type := PTree.t widget_info.
Definition empty_wgtenv := PTree.empty widget_info.

Definition trans_type (ty : typeL) : type :=
  LustreVGen.trans_type (LustreWGenDis.trans_type ty).

(* register widget interface and check for collision *)
Fixpoint register_varsenv (ve : varsenv) (vars : list (ident * typeL * clock)) : res varsenv :=
  match vars with
  | nil => OK ve
  | hv :: tv =>
      let (it, ck) := hv in
      let (id, ty) := it in
      match ve ! id with
      | None => 
        let ty' := trans_type ty in
        let ve' := PTree.set id (ty', ck) ve in
        register_varsenv ve' tv
      | Some _ => Error (MSG "duplicate names in widget interface: " :: CTX id :: nil)
      end
  end.

Fixpoint register_staticenv (ve : staticenv) (statics : list (ident * typeL)) : res staticenv :=
  match statics with
  | nil => OK ve
  | hv :: tv =>
      let (id, ty) := hv in
      match ve ! id with
      | None =>
        let ty' := trans_type ty in
        let ve' := PTree.set id ty' ve in
        register_staticenv ve' tv
      | Some _ => Error (MSG "duplicate names in widget interface: " :: CTX id :: nil)
      end
  end.

(* register a mapping to widget interface*)
(* note: no need to check collison between pi & ei *)
Fixpoint register_widgetenv (we : wgtenv) (itfl : list (ident * widgetT)) : res wgtenv :=
  match itfl with
  | nil => OK we
  | hi :: ti =>
      let (id, itf) := hi in
      match itf with
      | WidgetT _ statics params events => 
          do stats <- register_staticenv empty_staticenv statics;
          do pi <- register_varsenv empty_varsenv params;
          do ei <- register_varsenv empty_varsenv events;
          let we' := PTree.set id (mkwinfo None pi ei stats) we in
          register_widgetenv we' ti
      end
  end.

Definition trans_widgetenv (we0 : wgtenvW) : res wgtenv :=
  register_widgetenv empty_wgtenv (PTree.elements we0).

Fixpoint length_of_instances (subl : instanceTree) : nat :=
  match subl with
  | INil => O
  | ICons _ t => S (length_of_instances t)
  end.

(* check the widget exists and the subwidget length is same, in a DFS way*)
Fixpoint count_widget (m : markUp) (we : wgtenv) : res wgtenv :=
  match m with
  | GraphicsHierarchy wgt subl =>
      let wn := wgt_name wgt in
      let len := length_of_instances subl in
      match we ! wn with
      | None => Error (MSG "widget " :: CTX wn :: MSG " not found" :: nil) 
      | Some wi => 
          match wi.(subwgt_len) with
          | None => 
              let wi' := mkwinfo (Some len) wi.(params_info) wi.(events_info) wi.(statics_info) in
              let we' := PTree.set wn wi' we in
              count_widgets subl we'
          | Some len0 =>
              if beq_nat len len0 then count_widgets subl we
              else Error (msg "inconsistent subwidget list length detected!")
          end
      end
  end
with count_widgets (subl : instanceTree) (we : wgtenv) : res wgtenv :=
  match subl with
  | INil => OK we
  | ICons h t =>
      do we0 <- count_widget h we; 
      count_widgets t we0
  end.

(* utility for subl length access *)
Definition subwidgets_length (wn : ident) (we : wgtenv) : res nat :=
  match we ! wn with
  | None => Error (msg "ControlGen.subwidgets_length: widget not found!")
  | Some info =>
      match info.(subwgt_len) with
      | None => Error (msg "ControlGen.subwidgets_length: subwidgets length not known!")
      | Some len => OK len
      end
  end.

End WGTINFO.


Section API.

Definition null_signature := mksignature nil None cc_default.

Definition api_notify_get_event (dummy : unit) : ident * fundef :=
  let id := Lident.intern_string "notify_get_event" in
  (id,External (EF_external id null_signature) Tnil Tvoid).

Definition api_notify_update_change (dummy : unit) : ident * fundef :=
  let id := Lident.intern_string "notify_update_change" in
  (id,External (EF_external id null_signature) Tnil Tvoid).

Fixpoint id_seq_types (n : nat) : typelist :=
  match n with
  | O => Tnil
  | S m => Tcons type_int32s (id_seq_types m)
  end.

Definition api_create_widget (wgt : ident) (we : wgtenv) : res (ident * fundef) :=
  let id := Lident.intern_string (String.append "create_" (Lident.extern_atom wgt)) in
  do subl <- subwidgets_length wgt we;
  let tyl := id_seq_types (S subl) in
  OK (id,External (EF_external id null_signature) tyl Tvoid).

Definition query_event_type (wgt: ident) (evt: ident) (we : wgtenv) : res (type * clock) :=
  match we ! wgt with
  | None => assertion_failed
  | Some winfo => 
      let ei := events_info winfo in
      match ei ! evt with
      | None => assertion_failed
      | Some va => OK va
      end
  end.

Definition query_param_type (wgt: ident) (evt: ident) (we : wgtenv) : res (type * clock) :=
  match we ! wgt with
  | None => assertion_failed
  | Some winfo => 
      let pi := params_info winfo in
      match pi ! evt with
      | None => assertion_failed
      | Some va => OK va
      end
  end.

Definition api_getevent (wgt : ident) (evt : ident) (tk : type * clock) : ident * fundef :=
  let id := Lident.intern_string 
    (String.append 
      (String.append 
        (String.append 
          "getevent_" (Lident.extern_atom wgt)
        ) "_" 
      ) (Lident.extern_atom evt)
    ) 
  in
  let (ty, ck) := tk in
  let tyl := Tcons type_int32s Tnil in
  (id, External (EF_external id null_signature) tyl ty).

Definition api_update (wgt : ident) (param : ident) (tk : type * clock) : ident * fundef :=
  let id := Lident.intern_string 
    (String.append 
      (String.append 
        (String.append 
          "update_" (Lident.extern_atom wgt)
        ) "_" 
      ) (Lident.extern_atom param)
    )
  in
  let (ty, ck) := tk in
  let tyl := Tcons type_int32s (Tcons ty Tnil) in
  (id, External (EF_external id null_signature) tyl Tvoid).

(* extenv is just a container of external declaration, using the function name as key *)
Definition extenv := PTree.t fundef.
Definition empty_extenv := PTree.empty fundef.

End API.

Section CREATE_FUN.

(* the generation of create_gui function 
   this pass does not need meta info

   this pass update the extenv
*)
Definition num_of_markup (m : markUp) : ident :=
  match m with
  | GraphicsHierarchy wgt _ =>
      wgt.(wgt_num)
  end.

Fixpoint nums_of_subtree (subl : instanceTree) : list ident :=
  match subl with
  | INil => nil
  | ICons h t => 
      num_of_markup h :: nums_of_subtree t
  end.

Definition positive_to_expr (n : positive) : expr :=
  Econst_int (Int.repr (Zpos n)) type_int32s.

Definition exprlist_of_markup (m : markUp) : list expr :=
  let nm0 := num_of_markup m in
  match m with
  | GraphicsHierarchy _ subl =>
    let numl := nm0 :: nums_of_subtree subl in
    map positive_to_expr numl
  end.

Definition function_expr_of (def : ident * fundef) : expr :=
  let (id, df) := def in
  let fty := type_of_fundef df in
  Evar id fty.

Fixpoint generate_create_stmt (m : markUp) (we : wgtenv) (ex : extenv) : res (statement * extenv) :=
  match m with
  | GraphicsHierarchy wgt subl =>
      do (sub_stmts, ex0) <- generate_create_stmts subl we ex;
      do (fid, fdef) <- api_create_widget wgt.(wgt_name) we;
      let func := function_expr_of (fid, fdef) in
      (* set without checking, as the widget prototype should be the same after the wgtinfo pass *)
      let ex1 := PTree.set fid fdef ex0 in
      OK (Ssequence sub_stmts (Scall None func (exprlist_of_markup m)), ex1)
  end
with generate_create_stmts (subl : instanceTree) (we : wgtenv) (ex : extenv) : res (statement * extenv) :=
  match subl with
  | INil => OK (Sskip, ex)
  | ICons m0 subl' =>
      do (stmt0, ex0) <- generate_create_stmt m0 we ex;
      do (stmt1, ex1) <- generate_create_stmts subl' we ex0;
      OK (Ssequence stmt0 stmt1, ex1)
  end.

Definition create_func_gen (m : markUp) (we : wgtenv) (ex : extenv) : res (ident * fundef * extenv) :=
  let funcname := Lident.intern_string "create_gui_layout" in
  do (stmt, ex') <- generate_create_stmt m we ex;
  let func := mkfunction Tvoid nil nil nil stmt in
  OK ((funcname, Internal func), ex').

End CREATE_FUN.

Section MAIN_FUN.
  Definition in_struct_type (main_id : ident) : type :=
    Tpointer (Tstruct (Lident.acg_inc_name main_id) Fnil).

  Definition in_struct_expr (main_id : ident) : expr :=
    Evar (Lident.INSTRUCT) (in_struct_type main_id).

  Definition out_struct_type (main_id : ident) : type :=
    Tpointer (Tstruct (Lident.acg_outc_name main_id) Fnil).

  Definition out_struct_expr (main_id : ident) : expr :=
    Evar (Lident.OUTSTRUCT) (out_struct_type main_id).

  Definition ptr_field_expr (ptr : expr) (fn : ident) (fty : type) : res expr :=
    match Csim.typeof ptr with
    | Tpointer ty =>
        let deref_expr := Ederef ptr ty in
        OK (Efield deref_expr fn fty)
    | _ => Error (msg "ControlGen.ptr_field_expr: not a pointer type!")
    end.

  Section EVENT_GET.
    
    Record event_generator : Type := mkegenerator {
      ev_ie : idenv;
      ev_we : wgtenv;
      ev_ex : extenv;
      ev_temps : list (ident * type);
      ev_next : positive;
      ev_main : ident
    }.

    Definition temp_name (se : positive) : ident :=
      Lident.intern_string (String.append("event_temp_") (Lident.string_of_positive se)).

    Fixpoint generate_event_stmt (me : megaenvW) (eg : event_generator) : res (statement * event_generator) :=
      match me with
      | nil => OK (Sskip, eg)
      | ((wid, event), info) :: t =>
          match eg.(ev_ie) ! wid with
          | None => Error (msg "ControlGen.generate_event_stmt: id not found")
          | Some instance =>
              let wn := instance.(wgt_name) in
              do (ty, ck) <- query_event_type wn event eg.(ev_we);
              let (fname, fdef) := api_getevent wn event (ty, ck) in
              let ex' := PTree.set fname fdef eg.(ev_ex) in
              let tmp := temp_name eg.(ev_next) in
              let eg1 := mkegenerator eg.(ev_ie) eg.(ev_we) ex' ((tmp, ty) :: eg.(ev_temps)) (Psucc eg.(ev_next)) eg.(ev_main) in
              do (stmt', eg2) <- generate_event_stmt t eg1;
              let call_stmt := Scall (Some tmp) (function_expr_of (fname, fdef)) ((positive_to_expr instance.(wgt_num)) :: nil) in
              do ev_field <- ptr_field_expr (in_struct_expr eg.(ev_main)) info.(mid) ty;
              let assign_stmt := Sassign ev_field (Etempvar tmp ty) in
              OK (Ssequence (Ssequence call_stmt assign_stmt) stmt', eg2)
          end
      end.
  End EVENT_GET.

  Section GUI_UPDATE.
    Fixpoint generate_update_stmt (me : megaenvW) (ie : idenv) (we : wgtenv) (main_id : ident) (ex : extenv) : res (statement * extenv) :=
      match me with
      | nil => OK (Sskip, ex)
      | ((wid, param), info) :: t =>
          match ie ! wid with
          | None => Error (msg "ControlGen.generate_update_stmt : id not found!")
          | Some instance =>
              let wn := instance.(wgt_name) in
              do (ty, ck) <- query_param_type wn param we;
              let (fname, fdef) := api_update wn param (ty, ck) in
              do outval_expr <- ptr_field_expr (out_struct_expr main_id) info.(mid) ty;
              let wnum_expr := positive_to_expr instance.(wgt_num) in
              do (stmt', ex0) <- generate_update_stmt t ie we main_id ex;
              let ex' := PTree.set fname fdef ex0 in
              let call_stmt := Scall None (function_expr_of (fname, fdef)) (wnum_expr :: outval_expr :: nil) in
              OK (Ssequence call_stmt stmt', ex')
          end
      end.
  End GUI_UPDATE.

  Fixpoint trans_stmtlist (sl : list statement) : statement :=
    match sl with
    | nil => Sskip
    | h :: t => Ssequence h (trans_stmtlist t)
    end.

  Definition gen_ctrl_call (main_id : ident) : statement :=
    let param_tyl := Tcons (in_struct_type main_id) (Tcons (out_struct_type main_id) Tnil) in
    let func_expr := Evar main_id (Tfunction param_tyl Tvoid) in
    Scall None func_expr ((in_struct_expr main_id) :: (out_struct_expr main_id) :: nil).

  Definition main_loop_gen (main_id : ident) (mee meg : megaenvW) (ie : idenv) (we : wgtenv) (ex: extenv) : res (ident * fundef * extenv) :=
    let id := Lident.intern_string "main_loop" in
    let main_params := (Lident.INSTRUCT, in_struct_type main_id) :: (Lident.OUTSTRUCT, out_struct_type main_id) :: nil in
    do (stmt_event, eg) <- generate_event_stmt mee (mkegenerator ie we ex nil xH main_id);
    do (stmt_update, ex0) <- generate_update_stmt meg ie we main_id eg.(ev_ex);
    let temps := eg.(ev_temps) in
    (* add the notify_get_event statement and external def *)
    let (apiname, apidef) := api_notify_get_event tt in
    let ex1 := PTree.set apiname apidef ex0 in
    let getevent_call := Scall None (function_expr_of (apiname, apidef)) nil in
    (* add the notify_update_change statement and external def *)
    let (apiname', apidef') := api_notify_update_change tt in
    let ex2 := PTree.set apiname' apidef' ex1 in
    let updategui_call := Scall None (function_expr_of (apiname', apidef')) nil in
    (* generate the call to control node *)
    let control_call := gen_ctrl_call main_id in
    (* infinite loop *)
    let body := Swhile (Econst_int Int.one type_int32s) (trans_stmtlist (getevent_call :: stmt_event :: control_call :: stmt_update :: updategui_call :: nil)) in
    let def := Internal (mkfunction Tvoid main_params nil temps body) in
    OK ((id, def), ex2).

End MAIN_FUN.

Definition trans_control (m0 : markUp) (extinfo : extinfoW) : res program :=
  (* give every instance a unique id *)
  let m := generate_num m0 in
  (* generate id enviroment*)
  let ie := generate_idenv m empty_idenv in
  (* generate new widget environment *)
  do we0 <- trans_widgetenv extinfo.(wgt_itfW);
  (* add subwidget list length to we *)
  do we1 <- count_widget m we0;
  (* generate create function *)
  do (create_def, ex0) <- create_func_gen m we1 empty_extenv;
  (* generate main function *)
  do (main_def, ex1) <- main_loop_gen extinfo.(ctrl_name) extinfo.(ctrl_paramW) extinfo.(ctrl_returnW) ie we1 ex0; 
  let external_def := PTree.elements ex1 in
  OK (AST.mkprogram (map (fun def => (fst def, Gfun (snd def))) (external_def ++ create_def :: main_def :: nil)) xH).
