Require Import AST.
Require Import Cltypes.
Require Import Maps.
Require Import LustreS.

Definition nodeenv := PTree.t LustreS.node.
Definition empty_nodeenv := PTree.empty LustreS.node.

Definition constenv := PTree.t (globvar type).
Definition empty_constenv := PTree.empty (globvar type).

Inductive slot : Type :=
  | TConst : ident -> ident -> slot (*slot name, var name*)
  | TRefin : ident -> ident -> ident -> type -> slot (*slot name, node name, para name, type*)
  | TRefout : ident -> ident -> ident -> type -> slot
.

Inductive general_hierarchy { A : Type } : Type :=
  | TNode : A -> general_hierarchies -> list slot -> general_hierarchy
with general_hierarchies { A : Type } : Type :=
  | TNil : general_hierarchies
  | TCons : general_hierarchy -> general_hierarchies -> general_hierarchies
.

Fixpoint length { A : Type } (gh: @general_hierarchies A) : nat :=
  match gh with
  | TNil => O
  | TCons _ gh' => S (length gh')
  end.

Definition displayT := @general_hierarchy ident.
Definition displayListT := @general_hierarchies ident.

Record modelT : Type := mkmodelT {
  display : displayT;
  const_envT : constenv;
  node_envT : nodeenv
}.

Definition displayT' := @general_hierarchy (ident * ident).
Definition displayListT' := @general_hierarchies (ident * ident).

Record modelT' : Type := mkmodelT' {
  display' : displayT';
  const_envT' : constenv;
  nodes : list ident; (* TODO : node can only be instantiated once now, so the unique name needs no record *)
  structT : type
}.
