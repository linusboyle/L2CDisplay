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
Require Import Tree.
Require Import Lustre.
Require Import Lvalues.
Require Import LustreV.
Require Import LustreW.
Require Import Lident.
Require Import Toposort.
Require Import String.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Parameter bool_of_str: str -> bool.
Parameter int_of_str: str -> int.
Parameter float_of_str: str -> float32.
Parameter real_of_str: str -> float.
Parameter char_of_str: str -> int.

Section TRANSLATION.

Definition constenv:= PTree.t constL.

Definition empty_constenv:= PTree.empty constL.

Definition varsenv:= PTree.t (typeL*clock).

Definition handlerenv:= PTree.t (bool*list typeL).

Definition empty_varsenv:= PTree.empty (typeL*clock).

Definition empty_handlerenv:= PTree.empty (bool*list typeL).

Inductive env: Type := mkenv {
  global: varsenv;  
  local: varsenv;
  handler: handlerenv;
  const: constenv
}.

Definition trans_clock(c: singleclock): clock :=
  match c with 
  | Clock  ckb ckid => (ckb,(key ckid)) :: nil
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
  | Short => Tshort
  | UShort => Tushort
  | Int => Tint
  | UInt => Tuint
  | Float => Tfloat
  | Real => Treal
  | Char => Tchar
  end.

Definition trans_upop(op: unOp): unary_operationL :=
  match op with
  | AtomTypeOp a => 
    match a with
    | Bool => Obool
    | Short => Oshort
    | UShort => Oshort
    | Int => Oint
    | UInt => Oint
    | Float => Ofloat
    | Real => Oreal
    | Char => Ochar
    end
  | NOT  => Onot
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

Definition trans_prefixunop(op: prefixUnOp): unary_operationL  :=
  match op with
  | PSHORT => Oshort
  | PINT => Oint
  | PFLOAT => Ofloat
  | PREAL => Oreal
  | PNOT => Onot
  | PPOS => Opos
  | PNEG => Oneg
  end.

Definition trans_highorderop(op: highOrderOp): iterator_operation  :=
  match op with
  | MAP => Omap
  | RED => Ored
  | FILL => Ofill
  | FILLRED => Ofillred
  end.

Definition trans_prefixop(ge: env)(op: prefixOp): res suboperator :=
  match op with
  | Ident id => 
    match (handler ge) ! (key id) with
    | Some (nk, rtys)  =>  OK (Nodehandler (key id) nk rtys)
    | None => Error (msg"LustreWGen.trans_prefixop: id not found in nodenv") 
    end
  | UnOp uop => OK (PrefixL_unary (trans_prefixunop uop))
  | BinOp bop => OK (PrefixL_binary (trans_binop bop))
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
  | EChar id => OK (EconstT (Cint (char_of_str (name id))) Tchar)
  | EShort id => OK (EconstT (Cint (int_of_str (name id))) Tshort)
  | EUShort id => OK (EconstT (Cint (int_of_str (name id))) Tushort)
  | EInt id => OK (EconstT (Cint (int_of_str (name id))) Tint)
  | EUInt id => OK (EconstT (Cint (int_of_str (name id))) Tuint)
  | EFloat id => OK (EconstT (Csingle (float_of_str (name id))) Tfloat)
  | EReal id => OK (EconstT (Cfloat (real_of_str (name id))) Treal)
  end.
  
Definition trans_pattern(ge: env)(p: pattern) : res patn :=
  match p with
  | PIdent id => 
    match  (global ge) ! (key id) with
    | Some (Tenum idl,_) => OK (Paenum (key id) idl)
    | _ => Error (msg (String.append (extern_atom (key id)) " canot be found in typeblock"))
    end
  | PBool id => OK (Pabool (bool_of_str (name id)))
  | PChar id => OK (Pachar (char_of_str (name id)))
  | PInt id => OK (Paint (int_of_str (name id)))
  | DefaultPattern => OK Pany
  end.

Definition typeof_const(c: constL) : type :=
  match c with
  | ShortConstL _ => Cltypes.Tint I16 Signed
  | UshortConstL _ => Cltypes.Tint I16 Unsigned
  | IntConstL _ => Cltypes.Tint I32 Signed
  | UintConstL _ => Cltypes.Tint I32 Unsigned
  | CharConstL  _ => Cltypes.Tint I8 Signed
  | FloatConstL  _ => Cltypes.Tfloat F32
  | RealConstL _ => Cltypes.Tfloat F64
  | BoolConstL  _ => Cltypes.Tint IBool Signed
  | _ => Tvoid
  end.

Definition valof_const(c: constL) : val :=
  match c with
  | ShortConstL i => Vint i
  | UshortConstL i => Vint i
  | IntConstL i => Vint i
  | UintConstL i => Vint i
  | CharConstL  i => Vint i
  | FloatConstL f => Vsingle f
  | RealConstL f => Vfloat f
  | BoolConstL  b => if b then Vint Int.one else Vint Int.zero
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
  | CEAtom (EChar ident) => OK (CharConstL (char_of_str (name ident)))
  | CEAtom (EShort ident) => OK (ShortConstL (int_of_str (name ident)))
  | CEAtom (EUShort ident) => OK (UshortConstL (int_of_str (name ident)))
  | CEAtom (EInt ident) => OK (IntConstL (int_of_str (name ident)))
  | CEAtom (EUInt ident) => OK (UintConstL (int_of_str (name ident)))
  | CEAtom (EFloat ident) => OK (RealConstL (real_of_str (name ident)))
  | CEAtom (EReal ident) => OK (RealConstL (real_of_str (name ident)))
  | CEUnOpExpr op expr => 
    do x <- eval gc expr; 
    match op with
    | POS => OK x
    | NOT => 
      match x with
      | BoolConstL b => OK (BoolConstL (negb b))
      | _ => Error (msg"eval: should be a bool value") 
      end
    | NEG =>
      match x with
      | IntConstL i => OK (IntConstL (Int.neg i))
      | UintConstL i => OK (UintConstL (Int.neg i))
      | ShortConstL i => OK (ShortConstL (Int.neg i))
      | UshortConstL i => OK ( UshortConstL (Int.neg i))
      | FloatConstL f => OK (FloatConstL (Float32.neg f))
      | RealConstL f => OK (RealConstL (Float.neg f))
      | _ => Error (msg"eval: type mismatched for operator '-'")
      end
    | _ => Error (msg"eval: expr not supported")
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
        | UintConstL a, Some (Vint i) => OK (UintConstL i)
        | ShortConstL a, Some (Vint i) => OK (ShortConstL i)
        | UshortConstL a, Some (Vint i) => OK (UshortConstL i)
        | FloatConstL a, Some (Vsingle f) => OK (FloatConstL f)
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
  | ShortConstL i => OK i
  | UshortConstL i => OK i
  | IntConstL i => OK i
  | UintConstL i => OK i
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
  | Tree.Fnil => OK Fnil
  | Tree.Fcons id k ftl => 
    do k' <- trans_kind gc k;
    do ftl' <- trans_fieldlist gc ftl;
    OK (Fcons (key id) k' ftl')
  end.

Fixpoint trans_expr(ge: env)(exp: Tree.expr): res exprT :=
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
  | DynamicProjectExpr e el d =>
    do e' <- trans_expr ge e;
    do el' <- trans_exprlist ge el;
    do d' <- trans_expr ge d;
    OK (EarrayprojT e' el' d')
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
  | MergeExpr id e1 e2 => 
    do e1' <- trans_expr ge e1;
    do e2' <- trans_expr ge e2;
    let pat := PatternConT (Pabool true) e1' (PatternConT (Pabool false) e2' PatternNilT) in
    OK (EmergeT (key id) pat)
  | IfExpr cond e1 e2 => 
    do cond' <- trans_expr ge cond; 
    do e1' <- trans_expr ge e1;
    do e2' <- trans_expr ge e2;
    OK (EifT cond' e1' e2')
  | CaseExpr e cases =>
    do e' <- trans_expr ge e;
    do cases' <- trans_caselist ge cases;
    OK (EcaseT e' cases')
  | NameWithExpr id items d =>
    do (ty, ck) <- typeclock_of_env ge (key id);
    do items <- trans_withlist ge items;
    do d' <- trans_expr ge d;
    OK (EmixT (EvarT (key id) ty ck) items d')
  | ExprList el => 
    do el' <- trans_exprlist ge el;
    OK (ListExprT el')
  | PrefixExpr preop el =>
    do el' <- trans_exprlist ge el;
    do preop' <- trans_prefixop ge preop;
    OK (ApplyExprT (SuboperatorT preop') el')
  | HighOrderExpr hop pop i el =>
    let hop' := trans_highorderop hop in
    do pop' <- trans_prefixop ge pop;
    do i' <- eval_int (const ge) i;
    do el' <- trans_exprlist ge el;
    OK (ApplyExprT (IteratorT hop' pop' i') el') 
  | BoolredExpr i j e =>
    do e' <- trans_expr ge e;
    OK (EboolredT (int_of_str i) (int_of_str j) e')
  | DieseExpr e => 
    do e' <- trans_expr ge e; 
    OK (EdieseT e')
  | NorExpr e =>
    do e' <- trans_expr ge e; 
    OK (EnorT e')
  end

with trans_exprlist(ge: env)(el: exprlist) : res expr_listT :=
  match el with
  | Tree.Enil => OK Enil
  | Tree.Econs e el1 => 
    do e' <- trans_expr ge e; 
    do el' <- trans_exprlist ge el1;
    OK (Econs e' el')
  end

with trans_caselist(ge: env)(cases: caselist): res pattern_listT :=
  match cases with
  | CasesNil => OK PatternNilT
  | CasesCons pat e cases1 =>
    do e' <- trans_expr ge e; 
    do cases' <- trans_caselist ge cases1;
    do pat' <- trans_pattern ge pat;
    OK (PatternConT pat' e' cases')
  end

with trans_namelist(ge: env)(names: namelist): res struct_listT :=
  match names with
  | NamesNil => OK EstructNil
  | NamesCons id e names1 =>
    do e' <- trans_expr ge e;
    do names' <- trans_namelist ge names1;
    OK (EstructCons (key id) e' names')
  end

with trans_withlist(ge: env)(wl: withlist) : res label_index_listT :=
  match wl with
  | WithNil => OK Lnil
  | WithCons (FieldItem id) wl1 =>
    do wl' <- trans_withlist ge wl1;
    OK (LconsLabelT (key id) wl')
  | WithCons (AccessItem e) wl1 =>
    do e' <- trans_expr ge e;
    do wl' <- trans_withlist ge wl1;
    OK (LconsIndexT e' wl')
  end.

Fixpoint trans_lhs(ge: env)(l: list AST.ident): res vars :=
  match l with
  | nil => OK nil
  | id :: tl =>
    do (ty, ck) <- typeclock_of_env ge id;
    do tl' <- trans_lhs ge tl;
    OK ((id, ty, ck) :: tl')
  end.

Definition trans_eqstmt(ge: env)(eq: eqStmt): res equationT :=
  match eq with 
  | EqStmt idl el =>
    do lv <- trans_lhs ge (map key idl);
    do el' <- trans_expr ge el;
    OK (EquationT lv el')
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
  | NOVARBLK => OK nil
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

Definition callidof_prefixop(op: prefixOp): list AST.ident :=
  match op with
  | Ident id => key id :: nil
  | _ => nil
  end.

Fixpoint callidof(exp: Tree.expr): list AST.ident :=
  match exp with 
  | AtomExpr a => nil
  | UnOpExpr op e1 => callidof e1
  | BinOpExpr op e1 e2 => callidof e1 ++ callidof e2
  | FieldExpr e id => callidof e
  | DynamicProjectExpr e el d => callidof e ++ callidof_list el ++ callidof d
  | ArrAccessExpr e i =>  callidof e
  | ArrInitExpr e en =>  callidof e
  | ArrConstructExpr el => callidof_list el
  | NameConstructExpr items => callidof_struct items
  | PreExpr e => callidof e
  | FbyExpr el1 i el2 => callidof_list el1 ++ callidof_list el2
  | ArrowExpr e1 e2 => callidof e1 ++ callidof e2
  | WhenExpr e b id => callidof e
  | CurrentExpr e => callidof e 
  | MergeExpr id e1 e2 => callidof e1 ++ callidof e2
  | IfExpr cond e1 e2 => callidof cond ++ callidof e1 ++ callidof e2
  | CaseExpr e cases => callidof e ++ callidof_cases cases
  | NameWithExpr id items d => callidof_withs items ++ callidof d
  | ExprList el => callidof_list el
  | PrefixExpr preop el => callidof_prefixop preop ++ callidof_list el
  | HighOrderExpr hop pop i el => callidof_prefixop pop ++ callidof_list el
  | BoolredExpr i j e => callidof e
  | DieseExpr e => callidof e
  | NorExpr e => callidof e
  end

with callidof_list(el: exprlist) : list AST.ident :=
  match el with
  | Tree.Enil => nil
  | Tree.Econs e el1 => callidof e ++ callidof_list el1
  end

with callidof_cases(cases: caselist): list AST.ident :=
  match cases with
  | CasesNil => nil
  | CasesCons pat e cases1 => callidof e ++ callidof_cases cases1
  end

with callidof_struct(names: namelist): list AST.ident :=
  match names with
  | NamesNil => nil
  | NamesCons id e names1 => callidof e ++ callidof_struct names1
  end

with callidof_withs(wl: withlist) : list AST.ident :=
  match wl with
  | WithNil => nil
  | WithCons (FieldItem id) wl1 => callidof_withs wl1
  | WithCons (AccessItem e) wl1 => callidof e ++ callidof_withs wl1
  end.

Definition callidof_eq(eq: eqStmt) : list AST.ident :=
  match eq with
  | EqStmt _ e => callidof e
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

Definition trans_program(p: Tree.program) : res (AST.ident*programT) :=
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
    do nds <- trans_nodeblks (mkenv gv empty_varsenv gn gc) blk;
    do mainid <- mainidof blk;
    OK (key mainid, mkprogramT types consts' nds (key mainid))
  end.
