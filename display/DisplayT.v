Require Import AST.
Require Import Cltypes.
Require Import Maps.
Require Import LustreS.

Definition nodeenv := PTree.t LustreS.node.
Definition empty_nodeenv := PTree.empty LustreS.node.

Definition constenv := PTree.t (globvar type).
Definition empty_constenv := PTree.empty (globvar type).

Inductive displayT : Type :=
  | TNode : ident -> displayList -> list slot -> displayT
with slot : Type :=
  | TConst : ident -> ident -> slot (*slot name, var name*)
  | TRefin : ident -> ident -> ident -> type -> slot (*slot name, node name, slot name, type*)
  | TRefout : ident -> ident -> ident -> type -> slot
with displayList : Type :=
  | TNil : displayList
  | TCons : displayT -> displayList -> displayList
.

Record modelT : Type := mkmodelT {
  display : displayT;
  const_envT : constenv;
  node_envT : nodeenv
}.

Record modelT' : Type := mkmodelT' {
  display' : displayT;
  const_envT' : constenv;
  node_envT' : nodeenv;
  structT : type
}.
