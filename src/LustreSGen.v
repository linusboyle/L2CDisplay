(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

(** Translation from LustreV to LustreS. *)

Require Import Coqlib.
Require Import Ctypes.
Require Import Cltypes.
Require Import AST.
Require Import Errors.
Require Import List.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Bool.
Require Import Lop.
Require Import LustreV.
Require Import Lustre.
Require Import LustreS.
Require Import Lident.
Require Import Ltypes.
Require Import Cop.


Local Open Scope error_monad_scope.

Set Implicit Arguments.

Record generator : Type := mkgenerator {
  gen_next: ident;
  gen_trail: list (ident * type)
}.

Definition bind3 (A B C D: Type) (f: res (A * B * C)) (g: A -> B -> C -> res D) : res D :=
  match f with
  | OK (x, y, z) => g x y z
  | Error msg => Error msg
  end.

Notation "'do' ( X , Y , Z ) <- A ; B" := (bind3 A (fun X Y Z => B))
 (at level 200, X ident, Y ident, Z ident, A at level 100, B at level 200)
 : error_monad_scope.

Remark bind3_inversion:
  forall (A B C D: Type) (f: res (A*B*C)) (g: A -> B -> C -> res D) (z: D),
  bind3 f g = OK z ->
  exists x x1 x2, f = OK (x, x1, x2) /\ g x x1 x2 = OK z.
Proof.
  intros until z. destruct f; simpl.
  destruct p. simpl.
  destruct p; simpl; intros. exists a, b, c; auto.
  intros; discriminate.
Qed.

Definition gensym (ty: type)(g: generator): (ident*generator) :=
  (acg_temp_name (gen_next g), mkgenerator (Psucc (gen_next g)) ((acg_temp_name (gen_next g), ty) :: gen_trail g)).

Definition mkstmt := (ident*type) -> stmt.

Fixpoint cons_current(idl: list ident)(tcl: list (type*clock))(l1: list sexp): res (list mkstmt) :=
  match idl, tcl, l1 with
  | hd1::tl1, (ty,cks)::tl2, hd3::tl3 =>
    do ck <- headof cks (msg "LustreSGen.cons_current: cks null");
    let cond := clock_cond ck in
    let eq := (fun lh => Scurrent lh hd1 cond hd3) in
    do eqs <- cons_current tl1 tl2 tl3;
    OK (eq:: eqs)
  | nil, nil, nil => OK nil
  | _, _, _ => Error (msg "LustreSGen.cons_current")
  end.

Fixpoint cons_fby(idl: list (ident))(lx ly: list sexp): res (list mkstmt) :=
  match idl, lx, ly with
  | id::tl1, hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => LustreS.Sfby lh id hd2 hd3) in 
    do eqs <- cons_fby tl1 tl2 tl3;
    OK (eq:: eqs)
  | nil,nil,nil => OK nil
  | _,_,_ => Error (msg "LustreSGen.cons_fby")
  end.

Fixpoint cons_fbyn(idl: list (ident*ident*ident))(lx ly: list sexp) (n: int): res (list mkstmt) :=
  match idl, lx, ly with
  | ids::tl1, hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => LustreS.Sfbyn lh ids n hd2 hd3) in 
    do eqs <- cons_fbyn tl1 tl2 tl3 n;
    OK (eq:: eqs)
  | nil,nil,nil => OK nil
  | _,_,_ => Error (msg "LustreSGen.cons_fbyn")
  end.

Fixpoint cons_pre(idl: list ident)(lx: list sexp): res (list mkstmt) :=
  match idl, lx with
  | id::tl1, hd2::tl2 =>
    do eqs <- cons_pre tl1 tl2;
    OK ((fun lh => LustreS.Spre lh id hd2):: eqs)
  | nil,nil => OK nil
  | _,_ => Error (msg "LustreSGen.cons_pre")
  end.

Fixpoint cons_arrow(lx ly: list sexp): res (list mkstmt) :=
  match lx, ly with
  | hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => Sarrow lh hd2 hd3) in
    do eqs <- cons_arrow tl2 tl3;
    OK (eq::eqs)
  | nil, nil => OK nil
  | _,_ => Error (msg "LustreSGen.cons_arrow")
  end.

Fixpoint cons_ifelse(lx ly: list sexp)(cond: sexp): res (list mkstmt) :=
  match lx, ly with
  | hd2::tl2, hd3::tl3 =>
    let eq := (fun lh => Sassign lh (Eif cond hd2 hd3)) in
    do eqs <- cons_ifelse tl2 tl3 cond;
    OK (eq::eqs)
  | nil, nil => OK nil
  | _,_ => Error (msg "LustreSGen.cons_ifelse")
  end.

Definition trans_prefix_unary_fold(b: bool)(op: unary_operationL)(val: Lustre.sexp)(i: int): mkstmt :=
  match op with
  | Lop.Obool=> (fun x => Sfor b (Hfoldcast x val (Cltypes.Tint IBool Signed)) i) 
  | Lop.Ochar => (fun x => Sfor b (Hfoldcast x val (Cltypes.Tint I8 Signed)) i) 
  | Lop.Oshort => (fun x => Sfor b (Hfoldcast x val (Cltypes.Tint I16 Signed)) i) 
  | Lop.Oint => (fun x => Sfor b (Hfoldcast x val (Cltypes.Tint I32 Signed)) i)
  | Lop.Ofloat => (fun x => Sfor b (Hfoldcast x val (Cltypes.Tfloat F32)) i)
  | Lop.Oreal => (fun x => Sfor b (Hfoldcast x val (Cltypes.Tfloat F64)) i) 
  | Lop.Onot => (fun x => Sfor b (Hfoldunary x  Cop.Onotbool val) i)
  | Lop.Opos => (fun x => Sassign x (Expr val))
  | Lop.Oneg => (fun x => Sfor b (Hfoldunary x Cop.Oneg val) i)
  end.

Fixpoint construct_lhs (tcl : list (type*clock))(g: generator) : (generator * list Lustre.sexp * list (ident*type*clock)) :=
  match tcl with
  | nil => (g, nil, nil)
  | (t,ck) :: tl => 
    let (pid,g1) := gensym t g in
    let '(g2,la2,lvar2) := construct_lhs tl g1 in
    (g2, Svar pid t :: la2, (pid,t,ck) :: lvar2)
  end.

Definition cons_calhs(lv:vars)(tcl: list (type*clock))(g: generator): (generator * list sexp * list (ident*type*clock)) :=
  match lv with
  | nil => construct_lhs tcl g
  | _ => (g, nil, lv)
  end.

Fixpoint cons_stmt (lv: list (ident*type*clock)) (mkss: list mkstmt): res (list (stmt*clock)) :=
  match lv, mkss with
  | nil, nil => OK nil
  | (lh,c)::tl1, mks::tl2 => 
    do eqs <- cons_stmt tl1 tl2;
    OK ((mks lh,c) :: eqs) 
  | _,_ => Error (msg "LustreSGen.cons_stmt ")
  end.

Definition cons_lhs (lv:vars)(tcl: list (type*clock))(mkss: list mkstmt)(g: generator): res (generator * list sexp * list (stmt*clock)) :=
  let '(g1,es1,lv1) := cons_calhs lv tcl g in
  do eqs <- cons_stmt lv1 mkss;
  OK (g1, es1, eqs).

Definition trans_assigns(lv: vars)(la: list sexp)(eqs: list (stmt*clock))(g: generator) : res (generator*list sexp* list (stmt*clock)) :=
  match lv with
  | nil => OK (g, la, eqs)
  | _ => 
    do eqs1 <- cons_stmt lv (map (fun x lh => Sassign lh (Expr x)) la);
    OK (g, nil, eqs++eqs1)
  end. 

Definition cons_boolred_array(lv:vars)(a: sexp)(ck: clock)(eqs: list (stmt*clock))(i j: int)(g: generator)
  : res (generator*list sexp*list (stmt*clock)) :=
  let mty := typeof a in
  do (aty, k) <- typeof_array mty;
  let (id1,g1) := gensym type_int32s g in
  let fs := (Sfor true (Hboolred (id1, type_int32s) a) (Int.repr k), ck) in
  let cond1 := Sbinop Lop.Ole (Sconst (Cint i) type_int32s) (Svar id1 type_int32s) type_bool in
  let cond2 := Sbinop Lop.Ole (Svar id1 type_int32s) (Sconst (Cint j) type_int32s) type_bool in
  let cond := Sbinop Lop.Oand cond1 cond2 type_bool in
  trans_assigns lv (cond::nil) (eqs++fs::nil) g1.

Definition trans_operator(lv:vars)(b: bool)(op: operator)(i: int)(tcl: list (type*clock))(els: list sexp)(g: generator) : res (generator* list sexp* list (stmt*clock)) :=
  match op with
  | Oiteratorcall highorder c=>
    do tc <- headof tcl (msg "LustreSGen.trans_expr: iteratorS");
    match highorder with
    | Omap => (**r Hmapcall: lhs -> calldef -> list sexp -> hstmt *)
      let '(g1, es2, lhs2) := cons_calhs lv tcl g in
      let eq := (Sfor b (Hmapcall (map fst lhs2) c els) i, snd tc) in
      OK (g1, es2, eq::nil)
    | Ofill => (**r Hfillcall: ident*type -> ident*type -> lhs -> calldef -> sexp -> hstmt *)
      let '(g1, es2, lhs2) := cons_calhs lv tcl g in
      let lhs3 := map fst lhs2 in
      match lhs3,els with
      | hd::tl, hd1::nil =>
        let (id2,g2) := gensym (snd hd) g1 in
        let fvar := (id2, snd hd) in 
        let eq := (Sfor b (Hfillcall hd fvar tl c hd1) i, snd tc) in
        OK (g2, es2, eq::nil)
      | _, _ =>  Error (msg "LustreSGen.trans_operator: fill: call")
      end 
    | Ored => (**r Hredcall: ident*type -> ident*type -> calldef -> sexp -> list sexp -> hstmt *)
      let '(g1, es2, lhs2) := cons_calhs lv tcl g in
      let lhs3 := map fst lhs2 in
      match lhs3,els with
      | hd::nil, hd1::tl1 =>
        let (id2,g2) := gensym (snd hd) g1 in
        let fvar := (id2, snd hd) in 
        let eq := (Sfor b (Hredcall hd fvar c hd1 tl1) i, snd tc) in
        OK (g2, es2, eq::nil)
      | _, _ =>  Error (msg "LustreSGen.trans_operator: red: call")
      end   
    | Ofillred => (**r Hmapfoldcall: ident*type -> ident*type -> lhs -> calldef -> sexp -> list sexp -> hstmt *)
      let '(g1, es2, lhs2) := cons_calhs lv tcl g in
      let lhs3 := map fst lhs2 in
      match lhs3,els with
      | hd::tl, hd1::tl1 =>
        let (id2,g2) := gensym (snd hd) g1 in
        let fvar := (id2, snd hd) in 
        let eq := (Sfor b (Hmapfoldcall hd fvar tl c hd1 tl1) i, snd tc) in
        OK (g2, es2, eq::nil)
      | _, _ =>  Error (msg "LustreSGen.trans_operator: fillred: call")
      end  
    end 
  | Omapunary op=>
    let '(g2, es2, lhs2) := cons_calhs lv tcl g in
    do (hd1, ck1) <- headof lhs2 (msg "LustreSGen.trans_operator: mapunary: lhs2 null");
    do hd <- headof els (msg "LustreSGen.trans_operator: mapunary : els null");
    let hs := Hmapunary hd1 op hd in
    let eq := (Sfor b hs i, ck1) in
    OK (g2, es2, eq::nil)
  | Ofoldunary op=> (**r Hfoldunary: ident*type -> unary_operation -> sexp -> hstmt *)
    do hd2 <- headof els (msg "LustreSGen.trans_operator: foldunary");
    let mks := trans_prefix_unary_fold b op hd2 i :: nil in 
    cons_lhs lv tcl mks g
  | Omapary op=>
    match els with
    | hd2::hd3::_ =>
      let mks := (fun x => Sfor b (Hmapary x op hd2 hd3) i) :: nil in
      cons_lhs lv tcl mks g
    | _ => Error (msg "LustreSGen.trans_operator: mapary")
    end   
  | Ofoldary op=>(**r Hfoldary: ident*type -> binary_operation -> sexp -> sexp -> hstmt *)
    match els with
    | hd2::hd3::_ => 
      let mks := (fun x => Sfor b (Hfoldary x op hd2 hd3) i) :: nil in
      cons_lhs lv tcl mks g
    | _ => Error (msg "LustreSGen.trans_operator: foldary")
    end	  
  | Omaptycmp cmp => (**r Hmaptyeq: ident*type -> sexp -> sexp -> hstmt *)
    match els with
    | hd2::hd3::_ =>
      let mks := (fun x => Sfor b (Hmaptycmp x cmp hd2 hd3) i) :: nil in
      cons_lhs lv tcl mks g
    | _ => Error (msg "LustreSGen.trans_operator: iteratorS: maptycmp")
    end
  | Oarydef => (**r Sfor:bool -> (Harydef: ident*type ->sexp -> hstmt) -> int -> stmt *)
    do hd1 <- headof els (msg "LustreSGen.trans_operator: arydef");
    let mks := (fun x => Sfor b (Harydef x hd1) i) :: nil in
    cons_lhs lv tcl mks g
  | Oaryslc start =>  (**r Sor: bool -> (Haryslc: ident*type -> sexp -> int -> hstmt) -> int -> stmt*)
    do hd1 <- headof els (msg "LustreSGen.trans_operator: aryslc");
    let mks := (fun x => Sfor b (Haryslc x hd1 start) i) :: nil in
    cons_lhs lv tcl mks g
  end.
 
Fixpoint trans_expr (lv:vars)(exp: LustreV.expr) (g: generator){struct exp}: res (generator* list sexp* list (stmt*clock)) :=
  match exp with 
  | LustreV.Econst c t _ => (**r sexp *)
    let els := Sconst c t::nil in
    trans_assigns lv els nil g
  | LustreV.Evar v t _ => (**r sexp *)
    let els := Svar v t::nil in
    trans_assigns lv els nil g
  | LustreV.Eunop op e tc => (**r Scast: sexp-> type-> sexp; Sunop: unary_operation -> sexp -> type -> sexp *)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EunopS: es1 null");
    let es := trans_prefix_unary_expr op hd (fst tc) :: nil in
    trans_assigns lv es eqs1 g1
  | LustreV.Ebinop op e1 e2 tc => (**r Sbinop: binary_operation -> sexp -> sexp -> type -> sexp *)
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    do (g2, es2, eqs2) <- trans_expr nil e2 g1;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EbinopS");
    do hd1 <- headof es2 (msg "LustreSGen.trans_expr: EbinopS");
    let es := Sbinop op hd hd1 (fst tc) :: nil in 
    trans_assigns lv es (eqs1++eqs2) g2
  | LustreV.Earrayacc e i tc => (**r Saryacc: sexp -> sexp -> type -> sexp *)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do hd1 <- headof es1 (msg "LustreSGen.trans_expr: EarrayaccS: es1 null");
    let es := Saryacc hd1 (Sconst(Cint i) type_int32s) (fst tc) :: nil in
    trans_assigns lv es eqs1 g1
  | LustreV.Efield e id tc => (**r Sfield: sexp -> ident -> type -> sexp *)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EfieldS");
    let es := Sfield hd id (fst tc)::nil in 
    trans_assigns lv es eqs1 g1
  | LustreV.ListExpr el => (**r list sexp *)
    do (g1, els, eqs1) <- trans_expr_list el g;
    trans_assigns lv els eqs1 g1
  | LustreV.Ecall c el tcl=>
    do (g1, els1, eqs1) <- trans_expr_list el g;
    let '(g2, els2, lhs2) := cons_calhs lv tcl g1 in
    do tc <- headof tcl (msg "LustreSGen.trans_expr: EcallS");
    let eq:= (Scall (map fst lhs2) c els1, snd tc) in
    OK (g2, els2, eqs1++eq::nil)
  | LustreV.Efor b op i el tcl=>
    do (g1, els1, eqs1) <- trans_expr_list el g;
    do (g2, els2, eqs2) <- trans_operator lv b op i tcl els1 g1;
    OK (g2, els2, eqs1++eqs2)
  | LustreV.Econstruct estr tc => (**r Sstruct: ident*type -> list sexp -> stmt *)
    do (g1, es1, eqs1) <- trans_expr_list estr g;
    do fld <- fieldof_struct (fst tc);
    let mks := (fun x => Sstruct x fld es1) :: nil in
    do (g2, es2, eqs2) <- cons_lhs lv (tc::nil) mks g1;
    OK (g2, es2, eqs1++eqs2)
  | LustreV.Earraydiff el tc=> (**r Sarydif: ident*type -> list sexp -> stmt *)
    do (g1, es1, eqs1) <- trans_expr_list el g;
    let mks := (fun x => Sarydif x Int.zero es1) :: nil in 
    do (g2, es2, eqs2) <- cons_lhs lv (tc::nil) mks g1;
    OK (g2, es2, eqs1++eqs2)
  | LustreV.Earrayproj e1 el e2 tc=> (**r Earyprj: sexp -> list sexp -> sexp -> expr*)
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    do (g2, els, eqs2) <- trans_expr_list el g1;
    do (g3, es3, eqs3) <- trans_expr nil e2 g2;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EarrayprojS: es1 or es3 null");
    do hd1 <- headof es3 (msg "LustreSGen.trans_expr: EarrayprojS: es1 or es3 null");
    let mks := (fun x => Sassign x (Earyprj hd els hd1)) :: nil in
    do (g4, es4, eqs4) <- cons_lhs lv (tc::nil) mks g3;
    OK (g4, es4, eqs1++eqs2++eqs3++eqs4)
  | LustreV.Emix e1 lindex e2 tc=> (**r Smix: ident*type -> sexp -> list lindex -> sexp -> stmt*)
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    do (g2, lindexs, eqs2) <- trans_label_index_list lindex g1;
    do (g3, es3, eqs3) <- trans_expr nil e2 g2;
    do hd1 <- headof es1 (msg "LustreSGen.trans_expr: EmixS");
    do hd2 <- headof es3 (msg "LustreSGen.trans_expr: EmixS");
    let mks := (fun x => Smix x hd1 lindexs hd2) :: nil in
    do (g4, es4, eqs4) <- cons_lhs lv (tc::nil) mks g3;
    OK (g4, es4, eqs1++eqs2++eqs3++eqs4)
  | LustreV.Epre idl e tcl=> (**r Sfby: ident*type -> ident -> sexp -> sexp -> stmt *)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do mks <- cons_pre idl es1;
    do (g3, es3, eqs3) <- cons_lhs lv tcl mks g1;
    OK (g3, es3, eqs1++eqs3)
  | LustreV.Efby idl el1 el2 tcl=> (**r Sfby ident*type -> ident -> sexp -> sexp -> stmt *)
    do (g1, es1, eqs1) <- trans_expr_list el1 g;
    do (g2, es2, eqs2) <- trans_expr_list el2 g1;
    do mks <- cons_fby idl es1 es2;
    do (g3, es3, eqs3) <- cons_lhs lv tcl mks g2;
    OK (g3, es3, eqs1++eqs2++eqs3)
  | LustreV.Efbyn idl el1 i el2 tcl=> (**r Sfbyn ident*type -> (ident*ident*ident) -> int -> sexp -> sexp -> stmt *)
    do (g1, es1, eqs1) <- trans_expr_list el1 g;
    do (g2, es2, eqs2) <- trans_expr_list el2 g1;
    do mks <- cons_fbyn idl es1 es2 i;
    do (g3, es3, eqs3) <- cons_lhs lv tcl mks g2;
    OK (g3, es3, eqs1++eqs2++eqs3)
  | LustreV.Earrow e1 e2 tcl=> (**r Sarrow: ident*type -> sexp -> sexp -> stmt *)
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    do (g2, es2, eqs2) <- trans_expr nil e2 g1;
    do mks <- cons_arrow es1 es2;
    do (g3, es3, eqs3) <- cons_lhs lv tcl mks g2;
    OK (g3, es3, eqs1++eqs2++eqs3)
  | LustreV.Ewhen e1 cks tcl =>
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    trans_assigns lv es1 eqs1 g1
  | LustreV.Ecurrent idl e tcl => 
    do (g1, es1, eqs1) <- trans_expr nil e g;
    let tcl' := typeclock_of e in
    do mks <- cons_current idl tcl' es1;
    do (g3, es3, eqs3) <- cons_lhs lv tcl mks g1;
    OK (g3, es3, eqs1++eqs3)
  | LustreV.Emerge cid ty patl tcl=>
    let cond := Svar cid ty in
    do (g1, patls, eqs1) <- trans_pattern_list patl g;
    let mks := (fun x => Sassign x (Emerge cond patls)) :: nil in 
    do (g2, es2, eqs2) <- cons_lhs lv tcl mks g1;
    OK (g2, es2, eqs1++eqs2)
  | LustreV.Eif e1 e2 e3 tcl=> (**r Eif: sexp -> sexp -> sexp -> expr *)
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    do (g2, es2, eqs2) <- trans_expr nil e2 g1;
    do (g3, es3, eqs3) <- trans_expr nil e3 g2;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EifS"); 
    do mks <- cons_ifelse es2 es3 hd;
    do (g4, es4, eqs4) <- cons_lhs lv tcl mks g3;
    OK (g4, es4, eqs1++eqs2++eqs3++eqs4)
  | LustreV.Ecase e patl tcl=> (**r Ecase: sexp -> list (patternL*sexp) -> expr *)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do (g2, patls, eqs2) <- trans_pattern_list patl g1;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EcaseS: es1 null"); 
    let mks := (fun x => Sassign x (Ecase hd patls)) :: nil in 
    do (g3, es3, eqs3) <- cons_lhs lv tcl mks g2;
    OK (g3, es3, eqs1++eqs2++eqs3)
  | LustreV.Eboolred i j e (ty, ck) =>
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EboolredS: es1 null"); 
    cons_boolred_array lv hd ck eqs1 i j g1
  | LustreV.Ediese e (ty, ck) => (*boolred(0,1,n)[a1, ..., an]*)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EdieseS: es1 null"); 
    cons_boolred_array lv hd ck eqs1 Int.zero Int.one g1
  | LustreV.Enor e (ty, ck) => (*boolred(0,0,n)[a1, ..., an]*)
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EnorS: es1 null"); 
    cons_boolred_array lv hd ck eqs1 Int.zero Int.zero g1
  | LustreV.Etypecmp cmp e1 e2 tc =>
    do (g1, es1, eqs1) <- trans_expr nil e1 g;
    do (g2, es2, eqs2) <- trans_expr nil e2 g1;
    do hd <- headof es1 (msg "LustreSGen.trans_expr: EbinopS");
    do hd1 <- headof es2 (msg "LustreSGen.trans_expr: EbinopS");
    let mks := (fun x => Sassign x (Etypecmp cmp hd hd1)) :: nil in
    do (g3, es3, eqs3) <- cons_lhs lv (tc::nil) mks g2;
    OK (g3, es3, eqs1++eqs2++eqs3)
  | LustreV.Eprefix op el tc=>
    do (g1, els1, eqs1) <- trans_expr_list el g;
    let mks := (fun x => Sassign x (Eprefix op els1)) :: nil in 
    do (g2, els2, eqs2) <- cons_lhs lv (tc::nil) mks g1;
    OK (g2, els2, eqs1++eqs2)
  end

with trans_expr_list (exps: LustreV.expr_list) (g:generator): res (generator* list sexp* list (stmt*clock)) :=
  match exps with
  | Enil => OK (g, nil, nil)
  | Econs hd tl =>
    do (g1, es1, eqs1) <- trans_expr nil hd g;
    do (g2, es2, eqs2) <- trans_expr_list tl g1;
    OK (g2, es1++es2, eqs1++eqs2)
  end

with trans_pattern_list (patns:pattern_list) (g: generator): res (generator* list (patn*sexp)* list (stmt*clock)) :=
  match patns with
  | PatternNil => OK (g, nil, nil)
  | PatternCon pat e patl =>
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do (g2, patls, eqs2) <- trans_pattern_list patl g1;
    do hd <- headof es1 (msg "LustreSGen.trans_pattern_list ");
    OK (g2, (pat,hd)::patls, eqs1++eqs2)
  end

with trans_label_index_list (la_index: label_index_list) (g: generator): res (generator* list lindex* list (stmt*clock)) :=
  match la_index with
  | Lnil => OK (g, nil, nil)
  | LconsLabel id tl =>
    do (g2, es2, eqs2) <- trans_label_index_list tl g;
    OK (g2, (Label id)::es2, eqs2)
  | LconsIndex e tl =>
    do (g1, es1, eqs1) <- trans_expr nil e g;
    do (g2, es2, eqs2) <- trans_label_index_list tl g1;
    do hd1 <- headof es1 (msg "LustreSGen.trans_label_index_list: es1 null ");
    OK (g2, (Index hd1)::es2, eqs1++eqs2)
  end.

Fixpoint trans_equation_list (eqs: list equation) (g: generator): res (generator*(list (stmt*clock))) :=
  match eqs with
  | nil => OK (g, nil)
  | Equation lh_list exp ::tl =>
    do (g1, es1, eqs1) <- trans_expr lh_list exp g;
    do (g2, eqs2) <- trans_equation_list tl g1;
    OK (g2, eqs1++eqs2)
  end.

Definition trans_node (nd: ident*LustreV.node): res (ident*LustreS.node) :=
  let id := fst nd in
  let f := snd nd in
  let g := mkgenerator xH nil in
  let args := map fst (LustreV.nd_args f) in
  let rets := map fst (LustreV.nd_rets f) in
  do (g1, eqs2) <- trans_equation_list (nd_eqs f) g;
  let locals := map fst (LustreV.nd_vars f)++rev (gen_trail g1) in
  OK (id,mknode (LustreV.nd_kind f) args rets nil nil locals eqs2 xH Cltypes.Fnil nil).

Definition trans_program (p: LustreV.program) : res (LustreS.program) :=
  do nodes <- mmap trans_node p.(node_block);
  OK (Lustre.mkprogram p.(type_block) p.(const_block) nodes p.(node_main)).
