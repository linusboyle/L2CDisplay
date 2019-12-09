Require Import AST.
Require Import Clight.
Require Import Coqlib.
Require Import Ctypes.
Require Import GTree.
Require Import Errors.
Require Import Ident.
Require DisplaySGen.
Require DisplayTGen.
Require StructGen.
Require UpdateGen.

Local Open Scope error_monad_scope.

Definition trans_ext_func (ef : ident * fundef) : ident * globdef fundef type := 
  let nm := fst ef in
  (nm, Gfun (snd ef)).

Definition trans_program (model: GTree) (astS : LustreS.program): res program :=
  do mT  <- DisplayTGen.trans_model model astS;
  do mT' <- StructGen.generate_struct mT;
  do mS  <- DisplaySGen.trans_model mT';
  do mS' <- UpdateGen.trans_model mS;
  let efs := List.map trans_ext_func (DisplayS.external_funcS' mS') in
  let (cn, cf) := DisplayS.createFuncS' mS' in
  let createf := Gfun (Internal cf) in
  let (un, uf) := DisplayS.updateFuncS' mS' in
  let updatef := Gfun (Internal uf) in
  let st := DisplayS.structS' mS' in
  let gt := Gvar (mkglobvar st nil true true) in
  let cvars := List.map (fun it => (fst it, Gvar (snd it))) (DisplayS.const_valS' mS') in
  OK (mkprogram (cvars ++ (display_struct_name tt, gt) :: efs ++ (cn, createf) :: (un, updatef) :: nil) xH).

Definition merge (c1 c2 : program) : program :=
  mkprogram (c1.(prog_defs) ++ c2.(prog_defs)) c2.(prog_main).
