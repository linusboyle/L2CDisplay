Require Import AST.
Require Import Maps.
Require Import Ctypes.
Require Import Clight.
Require Import DisplayT.

Record slotS : Type := mkslotS {
  nm : ident;
  nd : ident;
  pa : ident;
  ty : type
}.

Record widget : Type := mkwidget {
  wty : ident; (* widget type name *)
  wid : ident; (* struct field name *)
  slin : list slotS;
  slout : list slotS;
  slconst : list (ident * ident * type) (* slot name * constenv entry *)
}.

Record modelS : Type := mkmodelS {
  widgetS : list widget;
  external_funcS : list (ident * fundef);
  createFuncS : ident * function;
  const_valS : list (ident * (globvar type));
  node_valS : nodeenv;
  node_mainS : ident;
  structS : type
}.

Record modelS' : Type := mkmodelS' {
  structS' : type;
  createFuncS' : ident * function;
  updateFuncS' : ident * function;
  external_funcS' : list (ident * fundef);
  const_valS' : list (ident * (globvar type))
}.
