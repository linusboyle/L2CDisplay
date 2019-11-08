Require Import AST.
Require Import Clight.
Require Import Coqlib.
Require Import Ctypes.
Require Import GTree.
Require Import Errors.
Require DisplaySGen.
Require DisplayTGen.
Require StructGen.

Local Open Scope error_monad_scope.

(*Definition main_def : function := *)
  (*{| fn_return := Tint I32 Signed noattr;*)
     (*fn_callconv := cc_default;*)
     (*fn_params := nil;*)
     (*fn_vars := nil;*)
     (*fn_temps := nil;*)
     (*fn_body := Sreturn (Some (Econst_int  Int.zero (Tint I32 Signed noattr)))*)
  (*|}.*)

(*Definition literal_var : globvar type :=*)
  (*mkglobvar (Tpointer (Tint I8 Signed noattr) noattr) (Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 41) :: nil) true true.*)

Definition trans_ext_func (ef : ident * fundef) : ident * globdef fundef type := 
  let nm := fst ef in
  (nm, Gfun (snd ef)).

Definition trans_program (model: GTree) (astS : LustreS.program): res program :=
  do mT  <- DisplayTGen.trans_model model astS;
  do mT' <- StructGen.generate_struct mT;
  do mS  <- DisplaySGen.trans_model mT';
  let efs := List.map trans_ext_func (DisplayS.external_funcS mS) in
  let (cn, cf) := DisplayS.createFuncS mS in
  let createf := Gfun (Internal cf) in
  let st := DisplayS.structS mS in
  let gt := Gvar (mkglobvar st nil true true) in
  OK (mkprogram (efs ++ (Lident.display_struct_name, gt) :: (cn, createf) :: nil) xH).
