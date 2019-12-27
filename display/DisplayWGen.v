
(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

(** Translation from Tree to LustreW. *)

Require Import Coqlib.
Require Import Ctypes.
Require Import Cltypes.
Require Import Errors.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Lop.
Require Import Lustre.
Require Import Lvalues.
Require Import LDisplay.
Require Import DisplayW.
Require Import Lident.
Require Import Toposort.
Require Import String.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Parameter bool_of_str: str -> bool.
Parameter int_of_str: str -> int.
Parameter real_of_str: str -> float.

Section TRANSLATION.

Definition constenv:= PTree.t constL.

Definition empty_constenv:= PTree.empty constL.

Definition varsenv:= PTree.t (typeL*clock).

Definition handlerenv:= PTree.t (bool*list typeL).

Definition empty_varsenv:= PTree.empty (typeL*clock).

Definition empty_handlerenv:= PTree.empty (bool*list typeL).

Record env: Type := mkenv {
  global: varsenv;  
  local: varsenv;
  handler: handlerenv;
  const: constenv
}.

Definition trans_clock(c: singleclock): clock :=
  match c with 
  | Clock ckb ckid => (ckb,(key ckid)) :: nil
  | NOCLOCK => nil
  end.

Definition trans_functype(fk: funcType) :=
  match fk with
  | Function => false
  | Node => true
  end.

Definition trans_atomtype(a: atomType): typeL :=
  match a with
  | Bool => Tbool
  | Int => Tint
  | Real => Treal
  end.

Definition trans_upop(op: unOp): unary_operationL :=
  match op with
  | NOT => Onot
  | POS => Opos
  | NEG => Oneg
  end.

Definition trans_binop(op: binOp) : binary_operationL :=
  match op with
  | ADD => Oadd
  | SUB => Osub
  | MUL => Omul
  | DIVF => Odivreal
  | DIV => Odivint
  | MOD => Omod
  | AND => Oand
  | OR => Oor
  | XOR => Oxor
  | GT => Ogt
  | LT => Olt
  | GE => Oge
  | LE => Ole
  | EQ => Oeq
  | NE => One
  end.

Definition typeclock_of_env(ge: env)(id: AST.ident) : res (typeL * clock) :=
  match (local ge) ! id with
  | Some tc => OK tc
  | None =>
    match (global ge) ! id with
    | Some tc => OK tc
    | None => Error (msg"LustreWGen.typeclock_of_env: id not found in env") 
    end
  end.

Definition is_enum_type(id: AST.ident)(ty: typeL) : bool * list AST.ident :=
  match ty with 
  | Tenum idl =>
    if in_list id idl then (true, idl) else (false,nil)
  | _ => (false,nil)
  end.

Definition trans_atomexpr(ge: env)(a: atomExpr): res exprT :=
  match a with
  | EIdent id => 
    do (ty, ck) <- typeclock_of_env ge (key id);
    let (is_enum, idl) := is_enum_type (key id) ty in
    if is_enum then 
      OK (EconstT (Cenum (key id) idl) ty)
    else
      OK (EvarT (key id) ty ck) 
  | EBool id => OK (EconstT (Cbool (bool_of_str (name id))) Tbool)
  | EInt id => OK (EconstT (Cint (int_of_str (name id))) Tint)
  | EReal id => OK (EconstT (Cfloat (real_of_str (name id))) Treal)
  end.
  
Definition typeof_const(c: constL) : type :=
  match c with
  | IntConstL _ => Cltypes.Tint I32 Signed
  | RealConstL _ => Cltypes.Tfloat F64
  | BoolConstL  _ => Cltypes.Tint IBool Signed
  | _ => Tvoid
  end.

Definition valof_const(c: constL) : val :=
  match c with
  | IntConstL i => Vint i
  | RealConstL f => Vfloat f
  | BoolConstL b => if b then Vint Int.one else Vint Int.zero
  | _ => Vmvl nil
  end.

Fixpoint eval(gc: constenv)(e: constExpr) : res constL := 
  match e with
  | CEAtom (EIdent ident) =>
    match gc ! (key ident) with
    | None => OK (ID (key ident))
    | Some expr => OK expr
    end
  | CEAtom (EBool ident) => OK (BoolConstL (bool_of_str (name ident)))
  | CEAtom (EInt ident) => OK (IntConstL (int_of_str (name ident)))
  | CEAtom (EReal ident) => OK (RealConstL (real_of_str (name ident)))
  | CEUnOpExpr op expr => 
    do x <- eval gc expr; 
    match op with
    | POS => OK x
    | NOT => 
      match x with
      | BoolConstL b => OK (BoolConstL (negb b))
      | _ => Error (msg"eval: 'not' operator expects a bool value") 
      end
    | NEG =>
      match x with
      | IntConstL i => OK (IntConstL (Int.neg i))
      | RealConstL f => OK (RealConstL (Float.neg f))
      | _ => Error (msg"eval: type mismatched for operator '-'")
      end
    end
  | CEBinOpExpr op exprL exprR =>
    do x <- eval gc exprL;
    do y <- eval gc exprR; 
    let t1 := typeof_const x in
    let t2 := typeof_const y in
    let op' := trans_binop op in
    let v1 := valof_const x in
    let v2 := valof_const y in
    if type_eq t1 t2 then
      match op with
      | ADD | SUB | MUL | DIVF | DIV | MOD =>
        match x, sem_binary_operation op' v1 v2 t1 t1 with
        | IntConstL a, Some (Vint i) => OK (IntConstL i)
        | RealConstL a, Some (Vfloat f) => OK (RealConstL f)
        | _, _ => Error (msg"eval: type mismatched for numeric operator")
        end
      | GT | LT | GE | LE  | AND | OR | XOR | EQ | NE =>
          match sem_binary_operation op' v1 v2 t1 type_bool with
          | Some (Vint i) => OK (BoolConstL (negb (Int.eq i Int.zero)))
          | _ => Error (msg"eval: type mismatched for bool operator")
          end
      end
    else Error (msg"eval: type mismatched ")
  | CEArray exprs =>
    do cl <- eval_list gc exprs;
    OK (ConstructConstL cl)
  | CEConstructor items =>
    do cl <- eval_struct gc items;
    OK (ConstructConstL cl)
  end

with eval_list(gc: constenv)(l: constExprlist) : res const_listL :=
  match l with
  | CEnil => OK ConstNilL
  | CEcons e l' => 
    do c <- eval gc e;
    do cl <- eval_list gc l';
    OK (ConstConL c cl)
  end

with eval_struct(gc: constenv)(l: cNameItems): res const_listL :=
  match l with
  | CNamesNil => OK ConstNilL
  | CNamesCons id e l' => 
    do c <- eval gc e;
    do cl <- eval_struct gc l';
    OK (ConstConL c cl)
  end.

Definition eval_int(gc: constenv)(e: constExpr): res int :=
  do c <- eval gc e;
  match c with
  | IntConstL i => OK i
  | _ => Error (msg"eval_int: not int value")
  end.

Fixpoint trans_kind(gc: constenv)(k: kind): res typeL :=
  match k with  
  | AtomType a => OK (trans_atomtype a)
  | Struct f =>
    do f' <- trans_fieldlist gc f;
    OK (Tstruct xH f')
  | Array k e => 
    do i <- eval_int gc e;
    do k' <- trans_kind gc k;
    OK (Tarray xH k' (Int.unsigned i))
  | EnumType idl => OK (Tenum (map (fun id => (key id) ) idl))
  | TypeDef id => Error (msg ("TypeDef has been process in TransTypeName!!"))
  end

with trans_fieldlist(gc: constenv)(f: fieldlist): res fieldlistL :=
  match f with
  | LDisplay.Fnil => OK Fnil
  | LDisplay.Fcons id k ftl => 
    do k' <- trans_kind gc k;
    do ftl' <- trans_fieldlist gc ftl;
    OK (Fcons (key id) k' ftl')
  end.

Definition trans_call(ge: env)(id: LDisplay.ident): res suboperator :=
  match (handler ge) ! (key id) with
  | Some (nk, rtys)  =>  OK (Nodehandler (key id) nk rtys)
  | None => Error (msg"DisplayWGen.trans_call: id not found in nodenv") 
  end.

Fixpoint trans_expr(ge: env)(exp: LDisplay.expr): res exprT :=
  match exp with 
  | AtomExpr a => trans_atomexpr ge a
  | UnOpExpr op e1 => 
    do e1' <- trans_expr ge e1;
    OK (EunopT (trans_upop op) e1')
  | BinOpExpr op e1 e2 =>
    do e1' <- trans_expr ge e1;
    do e2' <- trans_expr ge e2;
    OK (EbinopT (trans_binop op) e1' e2')
  | FieldExpr e id => 
    do e' <- trans_expr ge e;
    OK (EfieldT e' (key id))
  | ArrAccessExpr e i => 
    do e' <- trans_expr ge e;
    do i' <- eval_int (const ge) i;
    OK (EarrayaccT e' i')
  | ArrInitExpr e en => 
    do e' <- trans_expr ge e;
    do n <- eval_int (const ge) en;
    OK (EarraydefT e' n)
  | ArrConstructExpr el => 
    do el' <- trans_exprlist ge el;
    OK (EarraydiffT el')
  | NameConstructExpr items =>
    do items' <- trans_namelist ge items;
    OK (EconstructT items')
  | PreExpr e =>
    do e' <- trans_expr ge e;
    OK (EpreT e')
  | FbyExpr el1 i el2 =>
    do el1' <- trans_exprlist ge el1;
    do el2' <- trans_exprlist ge el2;
    do i' <- eval_int (const ge) i;
    OK (EfbyT el1' i' el2')
  | ArrowExpr e1 e2 => 
    do e1' <- trans_expr ge e1;
    do e2' <- trans_expr ge e2;
    OK (EarrowT e1' e2')
  | WhenExpr e b id =>
    do e' <- trans_expr ge e;
    OK (EwhenT e' ((b,key id)::nil))
  | CurrentExpr e =>
    do e' <- trans_expr ge e;
    OK (EcurrentT e')
  | IfExpr cond e1 e2 => 
    do cond' <- trans_expr ge cond; 
    do e1' <- trans_expr ge e1;
    do e2' <- trans_expr ge e2;
    OK (EifT cond' e1' e2')
  | ExprList el => 
    do el' <- trans_exprlist ge el;
    OK (ListExprT el')
  | Call id el =>
    do el' <- trans_exprlist ge el;
    do preop' <- trans_call ge id;
    OK (ApplyExprT preop' el')
  | DieseExpr e => 
    do e' <- trans_expr ge e; 
    OK (EdieseT e')
  | NorExpr e =>
    do e' <- trans_expr ge e; 
    OK (EnorT e')
  | MergeExpr id e1 e2 =>
    do e1' <- trans_expr ge e1;
    do e2' <- trans_expr ge e2;
    OK (EmergeT (key id) e1' e2')
  end

with trans_exprlist(ge: env)(el: exprlist) : res expr_listT :=
  match el with
  | LDisplay.Enil => OK Enil
  | LDisplay.Econs e el1 => 
    do e' <- trans_expr ge e; 
    do el' <- trans_exprlist ge el1;
    OK (Econs e' el')
  end

with trans_namelist(ge: env)(names: namelist): res struct_listT :=
  match names with
  | NamesNil => OK EstructNil
  | NamesCons id e names1 =>
    do e' <- trans_expr ge e;
    do names' <- trans_namelist ge names1;
    OK (EstructCons (key id) e' names')
  end.

Fixpoint trans_idents (ge: env) (l: list AST.ident) : res vars :=
  match l with
  | nil => OK nil
  | id :: tl =>
    do (ty, ck) <- typeclock_of_env ge id;
    do tl' <- trans_idents ge tl;
    OK ((id, ty, ck) :: tl')
  end.

Fixpoint trans_lhs(ge: env)(l: lhs): res vars :=
  match l with
  | LVIdent idl =>
      let ids := map key idl in
      trans_idents ge ids
  | LVMega _ => 
      Error (msg "Mega Variable not allowed in normal node!")
  end.

Fixpoint trans_rhs(ge: env)(r: rhs): res exprT :=
  match r with
  | RVExpr e =>
      trans_expr ge e
  | RVMega _ => 
      Error (msg "Mega Variable not allowed in normal node!")
  end.

Fixpoint trans_lhs_ctrl(ge: env)(l: lhs): res ctrl_lhs :=
  match l with
  | LVIdent idl =>
      let ids := map key idl in
      do vrs <- trans_idents ge ids;
      OK (IdentT vrs)
  | LVMega (Mega wgt field) => 
      OK (MegaLhsT (MegaT wgt.(key) field.(key)))
  end.

Fixpoint trans_rhs_ctrl(ge: env)(r: rhs): res ctrl_exprT :=
  match r with
  | RVExpr e =>
      do e' <- trans_expr ge e;
      OK (ExprT e')
  | RVMega (Mega wgt field)=> 
      OK (MegaExprT (MegaT wgt.(key) field.(key)))
  end.

Definition trans_eqstmt(ge: env)(eq: eqStmt): res equationT :=
  match eq with 
  | EqStmt lhs rhs =>
    do lv <- trans_lhs ge lhs;
    do el' <- trans_rhs ge rhs;
    OK (EquationT lv el')
  end.

Definition trans_eqstmt_ctrl(ge: env)(eq: eqStmt): res ctrl_equationT :=
  match eq with 
  | EqStmt lhs rhs =>
    do lv <- trans_lhs_ctrl ge lhs;
    do el' <- trans_rhs_ctrl ge rhs;
    OK (CtrlEquationT lv el')
  end.

Definition trans_static(gc: constenv)(static: ident*kind) : res (AST.ident*typeL) :=
  match static with 
  | (id, k) => 
    do ty <- trans_kind gc k;
    OK ((key id), ty)
  end.

Definition trans_var(gc: constenv)(var: ident*kind*singleclock) : res (AST.ident*typeL*clock) :=
  match var with 
  | (id, k, ck) => 
    do ty <- trans_kind gc k;
    OK ((key id), ty, (trans_clock ck))
  end.

Definition trans_varblk(gc: constenv)(vs: varBlk) : res vars :=
  match vs with 
  | VarList l => mmap (trans_var gc) l
  end.

Definition trans_typestmt(gc: constenv)(tystmt: typeStmt): res (AST.ident*typeL) :=
  match tystmt with 
  | TypeStmt id k =>
    do ty <- trans_kind gc k;
    OK (key id, ty)
  end.

Definition constblkof(nd: nodeBlk): list constStmt :=
  match nd with
  | ConstBlk cl => cl
  | _ => nil
  end.

Definition typeblkof(nd: nodeBlk): list typeStmt :=
  match nd with
  | TypeBlk tys => tys
  | _ => nil
  end.

Definition trans_conststmt(gc: constenv)(cs: constStmt): res (AST.ident*typeL*constL) :=
  match cs with
  | ConstStmt id k v =>
    do ty <- trans_kind gc k;
    do v' <- eval gc v;
    OK ((key id), ty, v')
  end.

Fixpoint add_vars(vars: list (AST.ident*typeL*clock))(e: varsenv) : varsenv :=
  match vars with
  | nil => e
  | (id, ty, ck) :: vtl => add_vars vtl (PTree.set id (ty,ck) e)
  end. 

Definition trans_nodeblk(ge: env)(nd: nodeBlk) : res (list nodeT) :=
  match nd with
  | FuncBlk ft id (ParamBlk ps) (ReturnBlk rs) (BodyBlk vas eqs) =>
    let nk := trans_functype ft in
    do paras <- mmap (trans_var (const ge)) ps;
    do rets <- mmap (trans_var (const ge)) rs;
    do vas' <- trans_varblk (const ge) vas;
    let te := add_vars (paras++rets++vas') empty_varsenv in
    let ge' := mkenv (global ge) te (handler ge) (const ge) in
    do eqs' <- mmap (trans_eqstmt ge') eqs;
    OK (NodeT nk (key id) paras rets vas' eqs' :: nil)
  | _ => OK nil
  end.

Fixpoint trans_nodeblks(ge: env)(nds: list nodeBlk) : res (list nodeT) :=
  match nds with
  | nil => OK nil
  | nd :: ndl =>
    do l1 <- trans_nodeblk ge nd;
    do l2 <- trans_nodeblks ge ndl;
    OK (l1 ++ l2)
  end.

End TRANSLATION.

Fixpoint ctrlblksof (nds : list nodeBlk) : list (ident * bodyBlk) :=
  match nds with
  | nil => nil
  | nd :: ndl =>
      let l0 := ctrlblksof ndl in
      match nd with
      | ControlBlk id body =>
          (id, body) :: l0
      | _ => l0
      end
  end.

Definition trans_control (ge : env) (nds: list nodeBlk) : res (AST.ident * ctrlT) :=
  match ctrlblksof nds with
  | (id, (BodyBlk vas eqs)) :: nil =>
    let id' := key id in
    do vas' <- trans_varblk (const ge) vas;
    let te := add_vars vas' empty_varsenv in
    let ge' := mkenv (global ge) te (handler ge) (const ge) in
    do eqs' <- mmap (trans_eqstmt_ctrl ge') eqs;
    OK ((key id), CtrlT (key id) vas' eqs')
  | _ => Error (msg "only one control node is allowed")
  end.

Definition trans_widget (gc : constenv) (gw : wgtenvW) (nd : nodeBlk) : res wgtenvW :=
    match nd with
    | WidgetBlk id (StaticBlk statics) (ParamBlk params) (ReturnBlk returns) =>
      do stats <- mmap (trans_static gc) statics;
      do rets <- mmap (trans_var gc) returns;
      do params <- mmap (trans_var gc) params;
      let wgt := WidgetT (key id) stats params rets in
      OK (PTree.set (key id) wgt gw)
    | _ => OK gw
    end.

Fixpoint trans_widget_block (gc : constenv) (gw : wgtenvW) (nds : list nodeBlk) : res wgtenvW :=
  match nds with
  | nil => OK gw
  | h :: t =>
      do gw0 <- trans_widget_block gc gw t;
      trans_widget gc gw0 h
  end.

Section TOPOCONSTS.

Local Open Scope string_scope.

Definition zero : str := "0".

Definition zeroid : ident := {| name := zero; key := xH |}.

Definition constnil := ConstStmt zeroid (AtomType Int) (CEAtom (EInt zeroid)).

Fixpoint constnamesof(c: constExpr) : list AST.ident :=
  match c with
  | CEAtom (EIdent id) => key id :: nil
  | CEUnOpExpr _ c1 => constnamesof c1
  | CEBinOpExpr _ c1 c2 => List.app (constnamesof c1) (constnamesof c2)    
  | CEConstructor cl => constnamesof_struct cl
  | CEArray cl => constnamesof_list cl
  | _ => nil
  end

with constnamesof_list(cl: constExprlist) : list AST.ident :=
  match cl with
  | CEnil => nil
  | CEcons c cl' => List.app (constnamesof c) (constnamesof_list cl')
  end

with constnamesof_struct(cl: cNameItems) : list AST.ident :=
  match cl with
  | CNamesNil => nil
  | CNamesCons id c cl' => List.app (constnamesof c) (constnamesof_struct cl')
  end.

Definition deps_of_const (consts: list constStmt)(n: nat): depend :=
  let c := nth n consts constnil in
  match c with
  | ConstStmt id ty v =>
    mkdepend (key id :: nil) (constnamesof v) n
  end.

Definition deps_of_consts (consts: list constStmt): list depend :=
  map (deps_of_const consts) (seq O (List.length consts)).

Definition toposort_consts (consts: list constStmt) : res (list constStmt):=
  let depl := deps_of_consts consts in 
  do depl' <- toposort_deps (List.length depl) depl; 
  let ids := map seqn depl' in 
  OK (map (fun id => nth id consts constnil) ids). 

Definition toposort_consts_nodeblk (ndblk: nodeBlk) : res (list constStmt):=
  let consts := constblkof ndblk in
  toposort_consts consts.

Fixpoint toposort_consts_nodeblks (ndblks: list nodeBlk) : res (list constStmt):=
  match ndblks with
  | nil => OK nil
  | ndblk :: tl => 
    do consts1 <- toposort_consts_nodeblk ndblk;
    do consts' <- toposort_consts_nodeblks tl; 
    OK (List.app consts1 consts')
  end.

End TOPOCONSTS.


Section MAINID.

Fixpoint callidof(exp: LDisplay.expr): list AST.ident :=
  match exp with 
  | AtomExpr a => nil
  | UnOpExpr op e1 => callidof e1
  | BinOpExpr op e1 e2 => callidof e1 ++ callidof e2
  | FieldExpr e id => callidof e
  | ArrAccessExpr e i =>  callidof e
  | ArrInitExpr e en =>  callidof e
  | ArrConstructExpr el => callidof_list el
  | NameConstructExpr items => callidof_struct items
  | PreExpr e => callidof e
  | FbyExpr el1 i el2 => callidof_list el1 ++ callidof_list el2
  | ArrowExpr e1 e2 => callidof e1 ++ callidof e2
  | WhenExpr e b id => callidof e
  | CurrentExpr e => callidof e 
  | IfExpr cond e1 e2 => callidof cond ++ callidof e1 ++ callidof e2
  | ExprList el => callidof_list el
  | Call id el => key id :: callidof_list el
  | DieseExpr e => callidof e
  | NorExpr e => callidof e
  | MergeExpr _ e1 e2 => callidof e1 ++ callidof e2
  end

with callidof_list(el: exprlist) : list AST.ident :=
  match el with
  | LDisplay.Enil => nil
  | LDisplay.Econs e el1 => callidof e ++ callidof_list el1
  end

with callidof_struct(names: namelist): list AST.ident :=
  match names with
  | NamesNil => nil
  | NamesCons id e names1 => callidof e ++ callidof_struct names1
  end.

Definition callidof_rhs (r : rhs) : list AST.ident :=
  match r with
  | RVMega _ => nil
  | RVExpr e => callidof e
  end.

Definition callidof_eq(eq: eqStmt) : list AST.ident :=
  match eq with
  | EqStmt _ rh => callidof_rhs rh
  end.

Definition deps_of_nodeblk (l: list nodeBlk)(n: nat): depend :=
  let a := nth n l (TypeBlk nil) in
  match a with
  | FuncBlk _ id _ _ (BodyBlk _ eqs) =>
    mkdepend (key id :: nil) (flat_map callidof_eq eqs) n
  | _ =>
    mkdepend nil nil n
  end.

Definition deps_of_nodeblks (l: list nodeBlk): list depend :=
  map (deps_of_nodeblk l) (seq O (List.length l)).

Definition toposort_nodeblks (l: list nodeBlk) : res (list nodeBlk):=
  let depl := deps_of_nodeblks l in 
  do depl' <- toposort_deps (List.length depl) depl; 
  let ids := map seqn depl' in 
  OK (map (fun id => nth id l (TypeBlk nil)) ids). 

Fixpoint mainidof_rec(blk: list nodeBlk): res ident :=
  match blk with
  | nil => Error (msg"canot find main id")
  | hd :: tl  => 
    match hd with
    | FuncBlk _ id _ _ _ => OK id
    | _  => mainidof_rec tl
    end
  end.

Definition mainidof(blk: list nodeBlk): res ident :=
  do blk' <- toposort_nodeblks blk;
  mainidof_rec (rev blk').

Fixpoint check_ctrl_depend (cid : AST.ident) (nds : list nodeBlk) : bool :=
  match nds with
  | nil => false
  | h :: t =>
      if check_ctrl_depend cid t then true
      else
        match h with
        | FuncBlk _ id _ _ (BodyBlk _ eqs) =>
            let callids := flat_map callidof_eq eqs in
            in_list cid callids
        | _ => false
        end
  end.

End MAINID.

Definition register_const(gc: constenv)(c: constStmt): res constenv :=
  match c with
  | ConstStmt id k e =>
    do ty <- trans_kind gc k;
    do v' <- eval gc e;
    OK (PTree.set (key id) v' gc)
  end.

Fixpoint register_consts(gc: constenv)(cl: list constStmt): res constenv :=
  match cl with
  | nil => OK gc
  | c :: cl' =>
    do gc1 <- register_const gc c;
    register_consts gc1 cl'
  end.

Definition add_nodehandler(nd: nodeBlk)(gc: constenv)(gn: handlerenv) : res handlerenv:=
  match nd with
  | FuncBlk ft id _ (ReturnBlk rs) _  =>
    let nk := trans_functype ft in
    do rets <- mmap (trans_var gc) rs;
    OK (PTree.set (key id) (nk, (map (fun x => snd (fst x)) rets)) gn)
  | _ => OK gn
  end.

Fixpoint register_nodehandlers(l: list nodeBlk)(gc: constenv)(gn: handlerenv) : res handlerenv :=
  match l with
  | nil => OK gn
  | nd :: tl =>
    do gn1 <- add_nodehandler nd gc gn;
    register_nodehandlers tl gc gn1
  end. 

Definition flat_enum(it: AST.ident*typeL): list (AST.ident*typeL) :=
  match snd it with
  | Tenum idl => map (fun id => (id, snd it)) (fst it :: idl)
  | _ => it :: nil
  end.

Fixpoint trans_enum_const(gv: varsenv)(item : constL)  : res constL :=
  match item with
  | ID id =>
    match gv ! id with
    | Some (ty, ck) =>
      let (is_enum, idl) := is_enum_type id ty in
      if is_enum then 
        OK (IntConstL (Int.repr (count_occ_pos idl id 0))) 
      else
        OK (ID id)
    | None => Error (msg "LustreVGen.trans_enum_const: id not found")
    end
  | ConstructConstL csl => 
    do csl' <- trans_enum_const_list gv csl;
    OK (ConstructConstL csl')
  | _ => OK item
  end 

with trans_enum_const_list(gv: varsenv) (const_list: const_listL) : res const_listL :=
  match const_list with
  | ConstNilL => OK ConstNilL
  | ConstConL l_item rest =>
    do l_item' <- trans_enum_const gv l_item;
    do rest' <- trans_enum_const_list gv rest;
    OK (ConstConL l_item' rest')
  end.

Definition trans_enum_const_block(gv: varsenv)(c: AST.ident*typeL*constL) : res (AST.ident* typeL*constL) :=
  match c with
  | (id, ty, v) =>
    do v' <- trans_enum_const gv v;
    OK (id, ty, v')
  end.

Definition trans_program(p: LDisplay.program) : res (AST.ident*programT) :=
  match p with
  | Program blk =>
    do consts <- toposort_consts_nodeblks blk;
    do gc <- register_consts empty_constenv consts;
    let tsl := flat_map typeblkof blk in
    do types <- mmap (trans_typestmt gc) tsl;
    do consts1 <- mmap (trans_conststmt gc) consts;
    let gtys := flat_map flat_enum types ++ map fst consts1 in
    let gv := add_vars (map (fun it => (it, global_clock)) gtys) empty_varsenv in
    do consts' <- mmap (trans_enum_const_block gv) consts1;
    do gn <- register_nodehandlers blk gc empty_handlerenv;
    let ge := mkenv gv empty_varsenv gn gc in
    do nds <- trans_nodeblks ge blk;
    do gw <- trans_widget_block gc empty_wgtenvW blk;
    do (cid, ctrl) <- trans_control ge blk;
    if check_ctrl_depend cid blk
    then Error (msg "normal node can not depend on control node")
    else OK (cid, mkprogramT types consts' nds ctrl gw cid)
  end.
