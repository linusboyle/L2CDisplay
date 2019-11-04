Require Import AST.
Require Import Clight.
Require Import Coqlib.
Require Import Ctypes.
Require Import GTree.
Require Import Errors.
Require Import Integers.
Require Import DisplayTGen.
Require Import StructGen.
Require Import String.
Require ClightGen.

Local Open Scope error_monad_scope.

Definition main_def : function := 
  {| fn_return := Tint I32 Signed noattr;
     fn_callconv := cc_default;
     fn_params := nil;
     fn_vars := nil;
     fn_temps := nil;
     fn_body := Sreturn (Some (Econst_int  Int.zero (Tint I32 Signed noattr)))
  |}.

Definition literal_var : globvar type :=
  mkglobvar (Tpointer (Tint I8 Signed noattr) noattr) (Init_int8 (Int.repr 42) :: Init_int8 (Int.repr 41) :: nil) true true.

Definition struct_name := Lident.intern_string "display_ctx".

Definition trans_program (model: GTree) (astS : LustreS.program): res program :=
  do mT <- trans_model model astS;
  do mT' <- generate_struct mT;
  let st := DisplayT.structT mT' in
  let gt := mkglobvar (ClightGen.trans_type st) nil true true in 
  let main_ident := Lident.intern_string "main" in
  let var_ident := Lident.intern_string "__stringlit_0" in
  OK (mkprogram ((struct_name, Gvar gt) :: (var_ident, Gvar literal_var) :: (main_ident, Gfun (Internal main_def)) :: nil) main_ident).
