Require Import AST.
Require Import Errors.
Require Import Cltypes.
Require Import Ctypes.
Require Import Csim.
Require Import Clight.
Require Import Coqlib.

Fixpoint trans_type (ty : Cltypes.type) : type :=
  match ty with
  | Cltypes.Tvoid => Tvoid
  | Cltypes.Tint size sign => Tint size sign noattr
  | Cltypes.Tfloat size => Tfloat size noattr
  | Cltypes.Tpointer ty' => Tpointer (trans_type ty') noattr
  | Cltypes.Tarray id t z => Tarray (trans_type t) z noattr
  | Cltypes.Tfunction tyl t => Tfunction (trans_typelist tyl) (trans_type t) cc_default
  | Cltypes.Tstruct id fld => Tstruct id (trans_fields fld) noattr
  end
with trans_typelist(l: Cltypes.typelist) : typelist :=
  match l with
  | Cltypes.Tnil => Tnil
  | Cltypes.Tcons t l' => Tcons (trans_type t) (trans_typelist l')
  end
with trans_fields (f: Cltypes.fieldlist) : fieldlist :=
  match f with
  | Cltypes.Fnil => Fnil
  | Cltypes.Fcons id t f' => Fcons id (trans_type t) (trans_fields f')
  end.

Fixpoint trans_expr (exp : Csim.expr) : expr :=
  match exp with
  | Csim.Econst_int va ty => Econst_int va (trans_type ty) 
  | Csim.Econst_float va ty => Econst_float va (trans_type ty)
  | Csim.Econst_single va ty => Econst_single va (trans_type ty)
  | Csim.Evar id ty => Evar id (trans_type ty) 
  | Csim.Etempvar id ty => Etempvar id (trans_type ty) 
  | Csim.Ederef exp' ty => Ederef (trans_expr exp') (trans_type ty)
  | Csim.Eaddrof exp' ty => Eaddrof (trans_expr exp') (trans_type ty) 
  | Csim.Eunop op exp' ty => Eunop op (trans_expr exp') (trans_type ty) 
  | Csim.Ebinop op exp1 exp2 ty => Ebinop op (trans_expr exp1) (trans_expr exp2) (trans_type ty) 
  | Csim.Ecast exp' ty => Ecast (trans_expr exp') (trans_type ty)
  | Csim.Efield exp' id ty => Efield (trans_expr exp') id (trans_type ty)
  end.

Fixpoint trans_statement (stmt : Csim.statement) : statement :=
  match stmt with
  | Csim.Sskip => Sskip
  | Csim.Sassign exp1 exp2 => Sassign (trans_expr exp1) (trans_expr exp2)
  | Csim.Sset id exp => Sset id (trans_expr exp)
  | Csim.Scall id ex exl => Scall id (trans_expr ex) (map trans_expr exl)
  | Csim.Ssequence stmt1 stmt2 =>
    Ssequence (trans_statement stmt1) (trans_statement stmt2)
  | Csim.Sifthenelse exp stmt1 stmt2 =>
    Sifthenelse (trans_expr exp) (trans_statement stmt1) (trans_statement stmt2)
  | Csim.Swhile exp stmt' => Swhile (trans_expr exp) (trans_statement stmt')
  end.

Definition trans_params (pl : list (ident * Cltypes.type)) : list (ident * type) := map (fun p => (fst p, trans_type (snd p))) pl.

Definition trans_fundef (def : Csim.fundef) : fundef :=
  match def with
  | Csim.Internal func =>
    Internal {|
      fn_return := trans_type func.(Csim.fn_return);
      fn_callconv := cc_default;
      fn_params := trans_params func.(Csim.fn_params);
      fn_vars := trans_params func.(Csim.fn_vars);
      fn_temps := trans_params func.(Csim.fn_temps);
      fn_body := trans_statement func.(Csim.fn_body)
    |}
  | Csim.External exfunc tyl ty =>
    External exfunc (trans_typelist tyl) (trans_type ty) cc_default
  end.

Definition trans_var (va : globvar Cltypes.type) : globvar type :=
  mkglobvar (trans_type va.(gvar_info)) va.(gvar_init) va.(gvar_readonly) va.(gvar_volatile).

Definition trans_globdef (def : ident * globdef Csim.fundef Cltypes.type) : ident * globdef fundef type :=
  let (id, func) := def in
  let func' :=
    match func with
    | Gfun funcdef => Gfun (trans_fundef funcdef)
    | Gvar var => Gvar (trans_var var)
    end
  in
  (id, func').

Definition trans_program (p : Csim.program) : program :=
  mkprogram (map trans_globdef p.(prog_defs)) p.(prog_main).
