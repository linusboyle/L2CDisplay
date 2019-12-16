Require Import AST.
Require Import Coqlib.
Require Import LustreW.
Require Import DisplayW.
Require Import Errors.
Require Import Lustre.
Require Import Maps.
Require Import Lident.
Require Import MarkUp.

Definition meta_info := meta_infoW.
Definition megaenv := megaenvW.

(* 
  this is the main part of LustreDisplay, translating
  control node to normal node, providing meta variable
  infos and widget interfaces to the markup language.

  the meta variables are eliminated: vars in lhs are 
  raised to return values, while vars in rhs are
  raised to parameters. The check of name collision is 
  done in the Lustre compiler.

  to do this, first generate a meta-to-id enviroment, giving
  every meta variable an id. lhs and rhs envs are separated.
  replace every occurrence of meta variable with "ctrl_arg_in/out_{id}".
*)

Definition ctrl_param_name (id : positive) : ident :=
  Lident.intern_string (String.append "ctrl_arg_in_" (Lident.string_of_positive id)).

Definition ctrl_return_name (id : positive) : ident :=
  Lident.intern_string (String.append "ctrl_arg_out_" (Lident.string_of_positive id)).

Record generator : Type := mkgenerator {
  me : megaenv;
  next_id : positive;
  we : widgetenv
}.

Fixpoint find_info (field : ident) (va : vars) : res (typeL * clock) :=
  match va with
  | nil => Error (CTX field :: MSG " not found" :: nil)
  | ((id, ty), ck) :: t =>
      if peq id field then OK (ty, ck)
      else find_info field t
  end.

Definition check_clock_ref (wid : ident) (ge : generator) (ck : bool * ident) : res (bool * ident) :=
  let (ct, ref) := ck in
  match find (wid, ref) ge.(me) with
  | None => Error (msg "the clock dependency is not satisfied in control node!")
  | Some info =>
      OK (ct, info.(mid))
  end.

Definition check_clock_refs (ck : clock) (wid : ident) (ge : generator) : res clock := mmap (check_clock_ref wid ge) ck.

Definition get_mega_info_lhs (mg : ident * ident) (we : widgetenv) : res (typeL * clock) :=
  let (kw, kf) := mg in
  match we ! kw with
  | None => Error (MSG "widget " :: CTX kw :: MSG " not found" :: nil)
  | Some (WidgetT id params events) =>
      find_info kf params
  end.

Definition get_mega_info_rhs (mg : ident * ident) (we : widgetenv) : res (typeL * clock) :=
  let (kw, kf) := mg in
  match we ! kw with
  | None => Error (MSG "widget " :: CTX kw :: MSG " not found" :: nil)
  | Some (WidgetT id params events) =>
      find_info kf events
  end.

Local Open Scope error_monad_scope.

Definition get_wgt_name (wgid : ident) (ie : idenv) : res ident :=
  match ie ! wgid with
  | None => Error (MSG "The instance " :: CTX wgid :: MSG " is not found" :: nil)
  | Some wgty => OK wgty
  end.

Definition register_lhs (gel : generator) (lhs : ctrl_lhs) (ie : idenv) : res generator :=
  match lhs with
  | IdentT va => OK gel
  | MegaLhsT (MegaT wgid fd) =>
      match find (wgid, fd) gel.(me) with
      | None => 
          do wgtn <- get_wgt_name wgid ie;
          do (ty, ck) <- get_mega_info_lhs (wgtn, fd) gel.(we);
          do ck' <- check_clock_refs ck wgid gel;
          let info := mkinfo (ctrl_return_name gel.(next_id)) ty ck' in
          let me' := add (wgid, fd) info gel.(me) in
          OK (mkgenerator me' (Psucc gel.(next_id)) gel.(we))
      | Some _ => OK gel
      end
  end.

Definition register_rhs (ger : generator) (rhs : ctrl_exprT) (ie : idenv) : res generator :=
  match rhs with
  | ExprT expr => OK ger
  | MegaExprT (MegaT wgid fd) =>
      match find (wgid, fd) ger.(me) with
      | None =>
          do wgtn <- get_wgt_name wgid ie;
          do (ty, ck) <- get_mega_info_rhs (wgtn, fd) ger.(we);
          do ck' <- check_clock_refs ck wgid ger;
          let info := mkinfo (ctrl_param_name ger.(next_id)) ty ck' in
          let me' := add (wgid, fd) info ger.(me) in
          OK (mkgenerator me' (Psucc ger.(next_id)) ger.(we))
      | Some _ => OK ger
      end
  end.

Definition register_equation (gel ger : generator) (eq : ctrl_equationT) (ie : idenv) : res (generator * generator) :=
  match eq with
  | CtrlEquationT lhs rhs =>
      do gel' <- register_lhs gel lhs ie;
      do ger' <- register_rhs ger rhs ie;
      OK (gel', ger')
  end.

Fixpoint register_equations (gel ger : generator) (eql : list ctrl_equationT) (ie : idenv) : res (generator * generator) :=
  match eql with
  | nil => OK (gel, ger)
  | h :: t =>
    do (gel', ger') <- register_equation gel ger h ie;
    register_equations gel' ger' t ie
  end.

Definition register_generators (ct : ctrlT) (we : widgetenv) (ie : idenv) : res (generator * generator) :=
  match ct with
  | CtrlT id varbk eqs =>
      let ge0 := mkgenerator nil xH we in 
      register_equations ge0 ge0 eqs ie
  end.

Definition trans_info (m : meta_info) : ident * typeL * clock := (m.(mid), m.(mty), m.(mclk)).

Definition trans_lhs (ge : generator) (lhs : ctrl_lhs) : res vars :=
  match lhs with
  | IdentT va => OK va
  | MegaLhsT (MegaT wg fd) =>
      match find (wg, fd) ge.(me) with
      | None => Error (msg "LustreWGenDis.trans_lhs: meta not found")
      | Some info => 
          OK (trans_info info :: nil)
      end
  end.

Definition trans_rhs (ge : generator) (rhs : ctrl_exprT) : res exprT :=
  match rhs with
  | ExprT e => OK e
  | MegaExprT (MegaT wg fd) =>
      match find (wg, fd) ge.(me) with
      | None => Error (msg "LustreWGenDis.trans_rhs: meta not found")
      | Some info =>
          OK (EvarT info.(mid) info.(mty) info.(mclk))
      end
  end.

Definition trans_eq (gel ger : generator) (eq : ctrl_equationT) : res equationT :=
  match eq with
  | CtrlEquationT lhs rhs =>
      do lhs' <- trans_lhs gel lhs; 
      do rhs' <- trans_rhs ger rhs; 
      OK (EquationT lhs' rhs')
  end.

(* translate controller to normal node, and produce metainfo *)
Definition trans_ctrl (ct : ctrlT) (gel ger: generator) (ie : idenv) : res (nodeT * extinfoW ) :=
  match ct with
  | CtrlT id varbk eqs =>
      do eqs' <- mmap (trans_eq gel ger) eqs;
      let params := map (fun it => trans_info (snd it)) ger.(me) in (* rhs (or events) will be parameters *)
      let returns := map (fun it => trans_info (snd it)) gel.(me) in (* and lhs will become the return values *)
      let ex := mkext gel.(we) ger.(me) gel.(me) ie in
      OK (NodeT true id params returns varbk eqs', ex)
  end.

Fixpoint trans_type (ty : typeL) : LustreW.typeL :=
  match ty with
  | Tint => LustreW.Tint
  | Treal => LustreW.Treal
  | Tbool => LustreW.Tbool
  | Tarray id ty num => 
      LustreW.Tarray id (trans_type ty) num
  | Tstruct id fil =>
      LustreW.Tstruct id (trans_fieldlist fil)
  | Tenum eil =>
      LustreW.Tenum eil
  end
with trans_fieldlist (fil : fieldlistL) : LustreW.fieldlistL :=
  match fil with
  | Fnil => LustreW.Fnil
  | Fcons id ty fil' =>
      LustreW.Fcons id (trans_type ty) (trans_fieldlist fil')
  end.

Definition trans_typeblk (tl : list (ident * typeL)) : list (ident * LustreW.typeL) := map (fun it => (fst it, trans_type (snd it))) tl.

Fixpoint trans_const (va : constL) : LustreW.constL :=
  match va with
  | IntConstL iv => LustreW.IntConstL iv
  | RealConstL fv => LustreW.RealConstL fv
  | BoolConstL bv => LustreW.BoolConstL bv
  | ConstructConstL cl => LustreW.ConstructConstL (trans_const_list cl) 
  | ID id => LustreW.ID id     
  end
with trans_const_list (cl : const_listL) : LustreW.const_listL :=
  match cl with
  | ConstNilL => LustreW.ConstNilL
  | ConstConL ch ct => LustreW.ConstConL (trans_const ch) (trans_const_list ct)
  end.

Definition trans_const_decl (con : ident * typeL * constL) : ident * LustreW.typeL * LustreW.constL :=
  let (id, ty) := fst con in
  let val := snd con in
  ((id, trans_type ty), trans_const val).

Definition trans_constblk (cl : list (ident * typeL * constL)) : list (ident * LustreW.typeL * LustreW.constL) :=
  map trans_const_decl cl.

Definition trans_var (va : ident * typeL * clock) : ident * LustreW.typeL * clock :=
  let (id, ty) := fst va in
  let ck := snd va in
  ((id, trans_type ty), ck).

Definition trans_vars (vas : list (ident * typeL * clock)) : list (ident * LustreW.typeL * clock) := map trans_var vas.

Definition trans_suboperator (op : suboperator) : LustreW.operatorT :=
  match op with
  | Nodehandler id ft tyl =>
      let subop' := LustreW.Nodehandler id ft (map trans_type tyl) in
      LustreW.SuboperatorT subop'
  end.

Fixpoint trans_expr (exp : exprT) : LustreW.exprT :=
  match exp with
  | EconstT con ty =>
      LustreW.EconstT con (trans_type ty)
  | EvarT id ty ck =>
      LustreW.EvarT id (trans_type ty) ck
  | ListExprT expl => 
      LustreW.ListExprT (trans_exprlist expl)
  | ApplyExprT op expl => 
      LustreW.ApplyExprT (trans_suboperator op) (trans_exprlist expl)
  | EconstructT sl =>
      LustreW.EconstructT (trans_structlist sl)
  | EarrayaccT exp' iv =>
      LustreW.EarrayaccT (trans_expr exp') iv
  | EarraydefT exp' iv =>
      LustreW.EarraydefT (trans_expr exp') iv
  | EarraydiffT expl => 
      LustreW.EarraydiffT (trans_exprlist expl)
  | EunopT op exp' =>
      LustreW.EunopT op (trans_expr exp')
  | EbinopT op exp1 exp2 => 
      LustreW.EbinopT op (trans_expr exp1) (trans_expr exp2)
  | EfieldT exp' id =>
      LustreW.EfieldT (trans_expr exp') id
  | EpreT exp' =>
      LustreW.EpreT (trans_expr exp')
  | EfbyT expl iv expl' =>
      LustreW.EfbyT (trans_exprlist expl) iv (trans_exprlist expl')
  | EarrowT exp1 exp2 =>
      LustreW.EarrowT (trans_expr exp1) (trans_expr exp2)
  | EwhenT exp' ck =>
      LustreW.EwhenT (trans_expr exp') ck
  | EcurrentT exp' =>
      LustreW.EcurrentT (trans_expr exp')
  | EifT exp1 exp2 exp3 => 
      LustreW.EifT (trans_expr exp1) (trans_expr exp2) (trans_expr exp3)
  | EdieseT exp' =>
      LustreW.EdieseT (trans_expr exp')
  | EnorT exp' =>
      LustreW.EnorT (trans_expr exp')
  end
with trans_exprlist (expl : expr_listT) : LustreW.expr_listT :=
  match expl with
  | Enil => LustreW.Enil
  | Econs exp expl' =>
      LustreW.Econs (trans_expr exp) (trans_exprlist expl')
  end
with trans_structlist (sl : struct_listT) : LustreW.struct_listT :=
  match sl with
  | EstructNil => LustreW.EstructNil
  | EstructCons id exp sl' =>
      LustreW.EstructCons id (trans_expr exp) (trans_structlist sl')
  end.

Definition trans_equation (eq : equationT) : LustreW.equationT :=
  match eq with
  | EquationT vas exp =>
      let vas' := trans_vars vas in
      LustreW.EquationT vas' (trans_expr exp)
  end.

Definition trans_node (nd : nodeT) : LustreW.nodeT :=
  match nd with
  | NodeT ft id params returns locals eqs => 
      let params' := trans_vars params in
      let returns' := trans_vars returns in
      let locals' := trans_vars locals in
      LustreW.NodeT ft id params' returns' locals' (map trans_equation eqs)
  end.

Definition trans_nodeblk (nds : list nodeT) : list LustreW.nodeT := map trans_node nds.

Definition trans_program (p : programT) (m : markUp) : res (LustreW.programT * extinfoW) :=
  let we := p.(widget_blockT) in
  let ie := generate_idenv m empty_idenv in
  do (gel, ger) <- register_generators p.(controlT) we ie;
  do (main_nd, ext) <- trans_ctrl p.(controlT) gel ger ie;
  let nds := main_nd :: p.(node_blockT) in
  let p' := LustreW.mkprogramT (trans_typeblk p.(type_blockT)) (trans_constblk p.(const_blockT)) (trans_nodeblk nds) p.(node_mainT) in
  OK (p', ext).
