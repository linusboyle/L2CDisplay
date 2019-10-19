Require Import AST.
Require Import Ctypes.
Require Import Cltypes.
Require Import Coqlib.
Require Import String.

Definition Tbool := Tint IBool Signed.
Definition Tchar := Tint I8 Signed.
Definition Tchar_str := Tpointer Tchar.

(*a reference to Lustre backend contains the target node name*)
(*and the input/output slot name*)
Inductive NodeRef : Type :=
  | NRconstruct: ident -> ident -> NodeRef
.

(* an output slot can be assigned constant value or associated with a node ref *)
Inductive OutputSlot(t: type): Type :=
  | STconst: string -> OutputSlot t
  | STref: NodeRef -> OutputSlot t (* node name and input/output name *)
.

(* an input slot can be ignored or associated with a node ref *)
Definition InputSlot(t: type): Type := option NodeRef.

(*TODO: add atomic and compound widgets*)
Inductive display: Type :=
  (*widgets*)
  | Button: OutputSlot Tchar_str -> InputSlot Tbool -> display (* a button has a text slot and click slot *)
  | Label: OutputSlot Tchar_str -> display (* a label has a text slot *)
  | Input: InputSlot Tchar_str -> InputSlot Tbool -> display (* an input line with its current text and 'submit' signal *)
  (*layouts*)
  | Vstack: display -> display -> display
  | Hstack: display -> display -> display
.

Definition typeof_input (t: type) (slot: InputSlot t) := t.

Definition typeof_output (t: type) (slot: OutputSlot t) := t.

(* an example *)
Definition dual_btn_horizontal := Hstack (Button (STconst _ "hello1"%string) None) (Button (STconst _ "hello2"%string) None).

Fixpoint btn_to_label (model: display) {struct model} : display := 
  match model with
  | Button text click => Label text
  | Label text => Label text
  | Input text submit => Input text submit
  | Vstack d1 d2 => Vstack (btn_to_label d1) (btn_to_label d2)
  | Hstack d1 d2 => Hstack (btn_to_label d1) (btn_to_label d2)
  end.
