Require Import AST.
Require Import Coqlib.
Require Import Integers.
Require Import Ctypes.
Require Import Display.
Require Import Clight.
Require Import String.

Parameter intern_string : string -> positive.

Definition main_def : function := 
  {| fn_return := Tint I32 Signed noattr;
     fn_callconv := cc_default;
     fn_params := nil;
     fn_vars := nil;
     fn_temps := nil;
     fn_body := Sreturn (Some (Econst_int  Int.zero (Tint I32 Signed noattr)))
  |}.

Definition hw_program : program :=
  let main_ident := intern_string "main" in
  mkprogram ((main_ident, Gfun (Internal main_def)) :: nil) main_ident.

Definition trans_program (model: display): program :=
  hw_program.
