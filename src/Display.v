Require Import String.

Inductive display: Set :=
  | Button: string -> display
  | Label: string -> display
  | Vstack: display -> display -> display
  | Hstack: display -> display -> display
.

Definition dual_btn_horizontal := Hstack (Button "hello1") (Button "hello2").

Fixpoint btn_to_label (model: display) {struct model} : display := 
  match model with
  | Button s => Label s
  | Label s => Label s
  | Vstack d1 d2 => Vstack (btn_to_label d1) (btn_to_label d2)
  | Hstack d1 d2 => Hstack (btn_to_label d1) (btn_to_label d2)
  end.
