Require Import AST.
Require Import Clight.
Require Import Coqlib.
Require Import Ctypes.
Require Import GTree.
Require Import Errors.
Require Import Integers.
Require Import DisplayTGen.
Require Import String.

Local Open Scope error_monad_scope.

Definition main_def : function := 
  {| fn_return := Tint I32 Signed noattr;
     fn_callconv := cc_default;
     fn_params := nil;
     fn_vars := nil;
     fn_temps := nil;
     fn_body := Sreturn (Some (Econst_int  Int.zero (Tint I32 Signed noattr)))
  |}.

Definition hw_program : program :=
  let main_ident := Lident.intern_string "main" in
  mkprogram ((main_ident, Gfun (Internal main_def)) :: nil) main_ident.

Definition trans_program (model: GTree) (astS : LustreS.program): res program :=
  do mT <- trans_model model astS;
  OK hw_program.
