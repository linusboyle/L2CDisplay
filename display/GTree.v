Require Import AST.
Require Import Integers.
Require Import Floats.

(*NOTE: the parser has ignored const value other than string*)
(*literal*)
Inductive constG :=
  | GBool : bool -> constG
  | GChar : int -> constG
  | GShort : int -> constG
  | GUShort : int -> constG
  | GInt : int -> constG
  | GUInt : int -> constG
  | GFloat : float32 -> constG
  | GReal : float -> constG
  | GString : ident -> constG
.

Inductive GTree :=
  | GNode : ident -> treeList -> list attribute -> GTree
with attribute :=
  | SConst : ident -> constG -> attribute
  | SNodeRef : ident -> ident -> ident -> attribute
with treeList :=
  | GNil : treeList
  | GCons : GTree -> treeList -> treeList 
.
