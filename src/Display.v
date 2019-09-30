Require Import String.

Definition slotid := string.

(*a reference to Lustre backend contains the target node name*)
(*and the input/output slot name*)
Inductive NodeRef : Type :=
  | NRconstruct: slotid -> slotid -> NodeRef
.

(* an output slot can be assigned constant value or associated with a node ref *)
Inductive OutputSlot(t: Type): Type :=
  | STconst: t -> OutputSlot t
  | STref: NodeRef -> OutputSlot t (* node name and input/output name *) 
.

(* an input slot can be ignored or associated with a node ref *)
Definition InputSlot(t: Type): Type := option NodeRef.

(*TODO: add more gui component*)
Inductive display: Type :=
  (*widgets*)
  | Button: OutputSlot string -> InputSlot bool -> display (* a button has a text slot and click slot *)
  | Label: OutputSlot string -> display (* a label has a text slot *)
  | Input: InputSlot string -> InputSlot bool -> display (* a input line with its current text and 'submit' signal *)
  (*layouts*)
  | Vstack: display -> display -> display
  | Hstack: display -> display -> display
.

(*an example*)
Definition dual_btn_horizontal := Hstack (Button (STconst _ "hello1"%string) None) (Button (STconst _ "hello2"%string) None).

Fixpoint btn_to_label (model: display) {struct model} : display := 
  match model with
  | Button text click => Label text
  | Label text => Label text
  | Input text submit => Input text submit
  | Vstack d1 d2 => Vstack (btn_to_label d1) (btn_to_label d2)
  | Hstack d1 d2 => Hstack (btn_to_label d1) (btn_to_label d2)
  end.
