Require Import AST.
Require Import Coqlib.

(*a reference to Lustre backend contains the target node name*)
(*and the input/output slot name*)
Inductive NodeRef : Type :=
  | NRconstruct: ident -> ident -> NodeRef
.

(* an output slot can be assigned constant value or associated with a node ref *)
Inductive OutputSlot: Type :=
  | STconst: ident -> OutputSlot
  | STref: NodeRef -> OutputSlot (* node name and input/output name *)
.

(* an input slot can be ignored or associated with a node ref *)
Definition InputSlot: Type := option NodeRef.

(*TODO: add atomic and compound widgets*)
Inductive display: Type :=
  (*widgets*)
  | Button: OutputSlot -> InputSlot -> display (* a button has a text slot and click slot *)
  | Label: OutputSlot -> display (* a label has a text slot *)
  | Input: InputSlot -> InputSlot -> display (* an input line with its current text and 'submit' signal *)
  (*layouts*)
  | Vstack: display -> display -> display
  | Hstack: display -> display -> display
.
