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

(** Translation from LustreW to LustreV. *)

Require Import Coqlib.
Require Import Datatypes.
Require Import Ctypes.
Require Import AST.
Require Import Errors.
Require Import List.
Require Import Integers.
Require Import Floats.
Require Import Maps.
Require Import Bool.
Require Import Lop.
Require Import LustreW.
Require Import Cltypes.
Require Import Ltypes.
Require Import Lustre.
Require Import LustreV.
Require Import Lident.

Local Open Scope error_monad_scope.

Set Implicit Arguments.

Fixpoint trans_type (ty:typeL) : type :=
  match ty with
  | LustreW.Tshort => Tint I16 Signed
  | LustreW.Tushort => Tint I16 Unsigned
  | LustreW.Tint => Tint I32 Signed
  | LustreW.Tuint => Tint I32 Unsigned
  | LustreW.Tfloat => Tfloat F32
  | LustreW.Treal => Tfloat F64
  | LustreW.Tbool => Tint IBool Signed
  | LustreW.Tchar => Tint I8 Signed
  | LustreW.Tarray id ty i => Tarray id (trans_type ty) i
  | LustreW.Tstruct id fdl => Tstruct id (trans_fieldlist fdl)
  | LustreW.Tenum idl => Tint I32 Signed
  end

with trans_fieldlist (fdl: fieldlistL) : fieldlist :=
  match fdl with
  | LustreW.Fnil => Fnil
  | LustreW.Fcons id ty fdl => Fcons id (trans_type ty) (trans_fieldlist fdl)
  end.


Definition typeof_unop(op: unary_operationL)(tc: type*clock): (type * clock) :=
  match op with
  | Obool => (Tint IBool Signed, snd tc)
  | Ochar => (Tint I8 Signed, snd tc)
  | Oshort => (Tint I16 Signed, snd tc) 
  | Oint => (Tint I32 Signed, snd tc)
  | Ofloat => (Tfloat F32, snd tc)
  | Oreal => (Tfloat F64, snd tc)
  | Onot => (Tint IBool Signed, snd tc)
  | Opos => tc
  | Oneg => tc
  end. 

Definition typeof_binop(op: binary_operationL)(tc: type*clock): (type * clock) :=
  match op with
  | Oadd | Osub | Omul | Omod => tc
  | Odivint =>
    match fst tc with
    | Tint _ _ => tc  
    | _ => (Tint I32 Signed, snd tc)
    end
  | Odivreal => (Tfloat F64, snd tc)
  | Oand | Oor | Oxor | Oeq | One| Olt| Ogt | Ole| Oge => (Tint IBool Signed, snd tc)
  end.   

Fixpoint field_find(fld: fieldlist)(id: ident) : res type := 
  match fld with
  | Fnil => Error (msg"LustreVGen: field_find: id not found in fieldlist") 
  | Fcons i ty ftl => if identeq id i then OK ty else field_find ftl id
  end.

Fixpoint cons_field(l: list (ident*type)): fieldlist := 
  match l with
  | nil => Fnil
  | (i, ty) :: tl => Fcons i ty (cons_field tl)
  end.

Definition tailof(A: Type)(l: list A)(msg: errmsg): res (list A) :=
  match l with
  | nil => Error msg
  | hd :: tl => OK tl
  end.

Definition typenv:= list (ident*type).

Fixpoint type_compare(t1 t2: type): bool :=
  match t1,t2 with
  | Tstruct _ fld1, Tstruct _ fld2 => type_list_compare fld1 fld2
  | Tint i1 s1, Tint i2 s2 => intsize_compare i1 i2 && sign_compare s1 s2 
  | Tfloat F32, Tfloat F32 => true
  | Tfloat F64, Tfloat F64 => true
  | Tarray _ at1 n1, Tarray _ at2 n2 => type_compare at1 at2 && Z.eqb n1 n2
  | _, _ => false 
  end

with type_list_compare(fld1 fld2: fieldlist): bool :=
  match fld1, fld2 with
  | Fnil,Fnil => true
  | Fcons id1 ty1 tl1, Fcons id2 ty2 tl2 => 
    identeq id1 id2 && type_compare ty1 ty2 && type_list_compare tl1 tl2
  | _, _ => false
  end.

Fixpoint find_type(ty: type)(l: typenv) : option type :=
  match l with
  | nil => None
  | (_,t)::tl => if type_compare ty t then Some t else find_type ty tl
  end.

Record generator : Type := mkgenerator {
  struct_next: ident;
  array_next: ident;
  fby_next: ident;
  call_next: ident;
  type_trail: typenv
}.

Definition genstruct (fld: fieldlist)(g: generator): (ident*generator) :=
  let sid := acg_struct_name (struct_next g) in
  let ty := Tstruct sid fld in
  (sid, mkgenerator (Psucc (struct_next g)) (array_next g) (fby_next g) (call_next g) (type_trail g++(sid,ty)::nil)).

Definition genarray (aty: type)(num: Z)(g: generator): (ident*generator) :=
  let aid := acg_array_name (array_next g) in
  let ty := Tarray aid aty num in
  (aid, mkgenerator (struct_next g) (Psucc (array_next g)) (fby_next g) (call_next g) (type_trail g++(aid,ty)::nil)).

Definition genfby(g: generator): (ident*generator) :=
  (acg_fby_name(fby_next g), mkgenerator (struct_next g) (array_next g) (Psucc (fby_next g)) (call_next g) (type_trail g)).

Definition gencall(g: generator): (ident*generator) :=
  (acg_context_name(call_next g), mkgenerator (struct_next g) (array_next g) (fby_next g) (Psucc (call_next g)) (type_trail g)).

Definition addtype (it: ident*type)(g: generator): generator :=
  mkgenerator (struct_next g) (array_next g) (fby_next g) (call_next g) (type_trail g++it::nil).

Fixpoint register_type(g: generator)(ty: type) : generator*type :=
  match ty with
  | Tstruct id fld =>
    match find_type ty (type_trail g) with
    | None =>
      let (g1,fld1) := register_fields g fld in
      if identeq id xH then 
        let (sid, g') := genstruct fld1 g1 in
        let ty := Tstruct sid fld1 in
        (g',ty)
      else
        let ty := Tstruct id fld1 in
        (addtype (id,ty) g1, ty)
    | Some t => (g,t)
    end
  | Tarray id aty num =>
    match find_type ty (type_trail g) with
    | None =>
      let (g1,aty1) := register_type g aty in
      if identeq id xH then 
        let (aid, g') := genarray aty1 num g1 in
        let ty := Tarray aid aty1 num in
        (g',ty)
      else
        let ty := Tarray id aty1 num in
        (addtype (id,ty) g1, ty)
    | Some t =>(g,t)
    end
  | _ => (g, ty)
  end

with register_fields(g: generator)(fld: fieldlist) : generator*fieldlist :=
  match fld with
  | Fnil => (g,Fnil) 
  | Fcons id ty ftl => 
    let (g1, ty1) := register_type g ty in
    let (g2, ftl1) := register_fields g1 ftl in
    (g2, Fcons id ty1 ftl1)
  end.

Fixpoint register_globaltype(id: ident)(g: generator)(ty: type) : (generator*type) :=
  match ty with
  | Tstruct _ fld =>
      let (g1,fld1) := register_fields g fld in
      let ty := Tstruct id fld1 in
      (addtype (id,ty) g1, ty)
  | Tarray _ aty num =>
      let (g1,aty1) := register_type g aty in
      let ty := Tarray id aty1 num in
      (addtype (id,ty) g1, ty)
  | _ => (addtype (id,ty) g, ty)
  end.

Fixpoint register_typeclocks(tcl: list (type*clock))(g: generator) : (generator*list(type*clock)) :=
  match tcl with
  | nil => (g, nil)
  | (ty,ck) :: tl =>
    let (g1,ty1) := register_type g ty in
    let (g2,tl') := register_typeclocks tl g1 in
    (g2, ((ty1,ck) :: tl'))
  end.  

Definition ids_of_fby (sty : type) : res (ident*ident) :=
  match sty with
  | Tstruct sid (Fcons _ _ (Fcons _ (Tarray aid _ _) Fnil)) =>
    OK (sid, aid)
  | _ => Error (msg"ids_of_fby error")
  end.

Fixpoint fby_mem_struct_vars(tcl: list (type*clock))(n: Z)(g: generator): res (generator * list (ident*ident*ident)):=
  match tcl with
  | nil => OK (g,nil)
  | (t,_) :: tl =>
     let (sid,g1) := genfby g in
     let idx := intern_string ("idx") in
     let items := intern_string ("items") in
     let fl := Fcons idx type_int32s (Fcons items (Tarray xH t n) Fnil) in
     let (g2, sty) := register_type g1 (Tstruct xH fl) in
     do (id1, aid) <- ids_of_fby sty;
     do (g3, svars) <- fby_mem_struct_vars tl n g2;
     OK (g3, (sid, id1, aid):: svars)
  end.

Fixpoint pre_mem_vars(tcl: list (type*clock))(g: generator): generator * list ident:=
  match tcl with
  | nil => (g, nil)
  | hd :: tyl =>
    let (preid, g1) := genfby g in
    let (g2, preids) := pre_mem_vars tyl g1 in
    (g2, preid :: preids)
  end.

Definition cons_boolred(e: expr): res (clock*expr) :=
  let tcl := typeclock_of e in 
  match tcl with
  | nil => Error (msg "LustreVGen.cons_boolred: expr is null")
  | (_,ck) :: nil => OK (ck, e)
  | (_,ck) :: tck :: _ => 
    let aty := Tarray xH type_bool (Z_of_nat (length tcl)) in 
    OK (ck, Earraydiff (Econs e Enil) (aty, ck)) 
   end.

Inductive classify_binop_case: Type :=
  | binop_case_normal
  | binop_case_typecmp: bool -> classify_binop_case.

Definition classify_binop(ty: type)(op: binary_operationL) :=
  match is_arystr ty, op with
  | true, Lop.Oeq => binop_case_typecmp true
  | true, Lop.One => binop_case_typecmp false
  | _, _ => binop_case_normal
  end.

Fixpoint merge_clock(ck: clock)(id: ident): clock :=
  match ck with
  | nil => nil
  | (b, ckid) :: cktl =>
    if identeq id ckid then cktl 
    else (b, ckid) :: merge_clock cktl id
  end.

Fixpoint trans_expr(exp: exprT)(g: generator){struct exp}: res (generator*expr) :=
  match exp with 
  | EconstT c ty => 
    OK (g, Econst c (trans_type ty) global_clock)
  | EvarT id ty ck =>
    let (g', ty') := register_type g (trans_type ty) in
    OK (g', Evar id ty' ck)
  | EunopT op e => 
    do (g1, e') <- trans_expr e g;  
    let tcl := typeclock_of e' in
    do tc <- headof tcl (msg "LustreVGen.trans_expr: EunopT: tcl null");
    let tc' := typeof_unop op tc in
    OK (g1, Eunop op e' tc')
  | EbinopT op e1 e2 =>
    do (g1, e1') <- trans_expr e1 g;
    do (g2, e2') <- trans_expr e2 g1;
    let tcl := typeclock_of e2' in
    do tc <- headof tcl (msg "LustreVGen.trans_expr: EbinopT: tcl null");
    let tc' := typeof_binop op tc in
    match classify_binop (fst tc) op with
    | binop_case_typecmp cmp => 
      OK (g2, Etypecmp cmp e1' e2' tc')
    | binop_case_normal =>
      OK (g2, Ebinop op e1' e2' tc')
    end
  | EarrayaccT e i => 
    do (g', e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    do tc <- headof tcl (msg "LustreVGen.trans_expr: EarrayaccT: tcl null");
    match tc with
    | (Tarray _ aty _, ck) =>  OK (g', Earrayacc e' i (aty, ck))
    | _ => Error (msg"LustreVGen: EarrayaccT: type is not array")
    end 
  | EfieldT e id =>
    do (g', e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    do tc <- headof tcl (msg "LustreVGen.trans_expr: EfieldT: tcl null");
    match tc with
    | (Tstruct _ fld, ck) =>
      do ty <- field_find fld id;
      OK (g', Efield e' id (ty, ck))
    | _ => Error (msg"LustreVGen: EarrayaccT: type is not array")
    end 
  | ListExprT el =>
    do (g', el') <- trans_expr_list el g;
    OK (g', ListExpr el')
  | ApplyExprT op el=>
    do (g', el') <- trans_expr_list el g;
    trans_operator op el' g'
  | EconstructT estr => 
    do (g1, idsel) <- trans_struct_list estr g;
    let (ids, el') := idsel in
    let tcl := typeclocks_of el' in
    let fld := cons_field (combine ids (map fst tcl)) in
    do (ty, ck) <- headof tcl (msg "LustreVGen.trans_expr: EconstructS: estr null"); 
    let (g', ty') := register_type g1 (Tstruct xH fld) in
    OK (g', Econstruct el' (ty',ck))
  | EarraydefT e i=> 
    do (g1, e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    do (ty, ck) <- headof tcl (msg "LustreVGen.trans_expr: EarraydefT: tcl null");
    let num := Int.unsigned i in 
    let (g', ty') := register_type g1 (Tarray xH ty num) in
    OK (g', Efor true Oarydef i (Econs e' Enil) ((ty',ck)::nil))
  | EarraydiffT el=> 
    do (g1, el') <- trans_expr_list el g;
    let tcl := typeclocks_of el' in
    do (ty, ck) <- headof tcl (msg "LustreVGen.trans_expr: EarraydefT: tcl null");
    let num := Z_of_nat (length tcl) in 
    let (g', ty') := register_type g1 (Tarray xH ty num) in
    OK (g', Earraydiff el' (ty',ck))
  | EarrayprojT e1 el e2=>
    do (g1, e1') <- trans_expr e1 g;
    do (g2, el') <- trans_expr_list el g1;
    do (g3, e2') <- trans_expr e2 g2;
    let tcl := typeclock_of e2' in
    do tc <- headof tcl (msg "LustreVGen.trans_expr: EarrayprojT: tcl null");
    OK (g3, Earrayproj e1' el' e2' tc)
  | EarraysliceT e i j=> 
    do (g1, e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    do (ty, ck) <- headof tcl (msg "LustreVGen.trans_expr: EarraysliceT: tcl null");
    match ty with
    | Tarray id aty _ => 
      if Int.lt i (Int.add j Int.one) then
        let num := Int.sub (Int.add j Int.one) i in 
        let (g', ty') := register_type g1 (Tarray xH aty (Int.unsigned num)) in
        OK (g', Efor true (Oaryslc i) num (Econs e' Enil) ((ty', ck)::nil))
      else Error (msg "LustreVGen.trans_expr: EarraysliceT: j < i")
    | _ => Error (msg "LustreVGen.trans_expr: EarraysliceT: not array")
    end
  | EmixT e1 lindex e2=>
    do (g1, e1') <- trans_expr e1 g;
    do (g2, lindex') <- trans_label_index_list lindex g1;
    do (g3, e2') <- trans_expr e2 g2;
    let tcl := typeclock_of e1' in
    do tc <- headof tcl (msg "LustreVGen.trans_expr: EmixT: tcl null");
    OK (g3, Emix e1' lindex' e2' tc)
  | EpreT e =>
    do (g1, e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    let (g2, preids) := pre_mem_vars tcl g1 in
    OK (g2, Epre preids e' tcl) 
  | EfbyT el1 i el2=> 
    do (g1, el1') <- trans_expr_list el1 g;
    do (g2, el2') <- trans_expr_list el2 g1;
    let tcl := typeclocks_of el1' in
    if (Z_eq_dec 1 (Int.unsigned i)) then
      let (g3,tyidl) := pre_mem_vars tcl g2 in
      OK (g3, Efby tyidl el1' el2' tcl)
    else
      do (g3,tyidl) <- fby_mem_struct_vars tcl (Int.unsigned i) g2;
      OK (g3, Efbyn tyidl el1' i el2' tcl)
  | EarrowT e1 e2=> 
    do (g1, e1') <- trans_expr e1 g;
    match e2 with
    | EpreT e3 =>
      do (g2, e3') <- trans_expr e3 g1;
      let tcl := typeclock_of e3' in 
      let (g3,tyidl) := pre_mem_vars tcl g2 in
      OK (g3, Efby tyidl (Econs e3' Enil) (Econs e1' Enil) tcl)
    | _ =>
      do (g2, e2') <- trans_expr e2 g1;
      let tcl := typeclock_of e2' in
      OK (g2, Earrow e1' e2' tcl)
    end
  | EwhenT e1 cks =>
    do (g1, e1') <- trans_expr e1 g;
    let tcl := typeclock_of e1' in
    let tcl' := map (fun tc => (fst tc, cks ++ snd tc)) tcl in
    OK (g1, Ewhen e1' cks tcl')
  | EcurrentT e => 
    do (g1, e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    do tcl' <- mmap (fun tc => 
                         do cktl <- tailof (snd tc) (msg "LustreVGen.trans_expr: EcurrentT: cks null");
                         OK (fst tc, cktl)) tcl;
    let (g2, preids) := pre_mem_vars tcl' g1 in
    OK (g2, Ecurrent preids e' tcl')
  | EmergeT cid patl=>
    do (g1, tcpatl) <- trans_pattern_list patl g;
    let (tc, patl') := tcpatl in
    let ck := merge_clock (snd tc) cid in
    OK (g1, Emerge cid type_bool patl' ((fst tc, ck)::nil))
  | EifT e1 e2 e3=> 
    do (g1, e1') <- trans_expr e1 g;
    do (g2, e2') <- trans_expr e2 g1;
    do (g3, e3') <- trans_expr e3 g2;
    let tcl := typeclock_of e2' in
    OK (g3, Eif e1' e2' e3' tcl)
  | EcaseT e patl=>
    do (g1, e') <- trans_expr e g;
    do (g2, tcpatl) <- trans_pattern_list patl g1;
    let (tc, patl') := tcpatl in
    OK (g2, Ecase e' patl' (tc::nil))
  | EboolredT i j e =>
    do (g1, e1) <- trans_expr e g;
    do (ck, e') <- cons_boolred e1;
    OK (g1, Eboolred i j e' (type_bool, ck))
  | EdieseT e =>
    do (g1, e1) <- trans_expr e g;
    do (ck, e') <- cons_boolred e1;
    OK (g1, Ediese e' (type_bool, ck))
  | EnorT e => 
    do (g1, e1) <- trans_expr e g;
    do (ck, e') <- cons_boolred e1;
    OK (g1, Enor e' (type_bool,ck))
  end

with trans_expr_list(exps: expr_listT)(g:generator): res (generator*expr_list) :=
  match exps with
  | LustreW.Enil => OK (g, Enil)
  | LustreW.Econs e el =>
    do (g1, e') <- trans_expr e g;
    do (g2, el') <- trans_expr_list el g1;
    OK (g2, Econs e' el')
  end

with trans_struct_list(sl: struct_listT)(g:generator): res (generator* ((list ident) * expr_list)) :=
  match sl with
  | LustreW.EstructNil => OK (g, (nil, Enil))
  | LustreW.EstructCons id e el =>
    do (g1, e') <- trans_expr e g;
    do (g2, idsel) <- trans_struct_list el g1;
    let (ids, el') := idsel in
    OK (g2, (id :: ids, Econs e' el'))
  end

with trans_pattern_list(patns:pattern_listT)(g:generator): res (generator*((type*clock)*pattern_list)) :=
  match patns with
  | PatternNilT => OK (g, ((type_int32s,global_clock),PatternNil))
  | PatternConT pat e patl =>
    do (g1, e') <- trans_expr e g;
    let tcl := typeclock_of e' in
    do (ty, ck) <- headof tcl (msg "LustreSGen.trans_pattern_list: tcl null ");
    do (g2, tcpatl) <- trans_pattern_list patl g1;
    let ( _, patl') := tcpatl in
    OK (g2, (ty, ck, PatternCon pat e' patl'))
  end

with trans_label_index_list(la_index: label_index_listT)(g:generator): res (generator*label_index_list) :=
  match la_index with
  | LustreW.Lnil => OK (g, Lnil)
  | LustreW.LconsLabelT id tl =>
    do (g1, tl') <- trans_label_index_list tl g;
    OK (g1, LconsLabel id tl')
  | LustreW.LconsIndexT e tl =>
    do (g1, e') <- trans_expr e g;
    do (g2, tl') <- trans_label_index_list tl g1;
    OK (g2, LconsIndex e' tl')
  end

with trans_operator(op: operatorT)(els: expr_list)(g:generator): res (generator*expr) :=
  let tcl := typeclocks_of els in
  match op with
  | SuboperatorT subop =>
    match subop with
    | LustreW.Nodehandler id nk rts  =>
      let (isid, g1) := gencall g in
      let ck := match tcl with
            | nil => global_clock
            | (ty,ck) :: tl => ck
            end in
      let tcl1 := map (fun ty => (trans_type ty, ck)) rts in
      let (g2, tcl') := register_typeclocks tcl1 g1 in
      let c := mkcalldef nk isid id None xH Cltypes.Fnil nil nil in
      OK (g2, Ecall c els tcl')
    | LustreW.PrefixL_unary unop =>
      do tc <- headof tcl (msg "LustreVGen.trans_expr: ApplyExprT: prefixL_unary");
      let tc' := typeof_unop unop tc in
      OK (g,  Eunop unop (ListExpr els) tc')
    | LustreW.PrefixL_binary binop => 
      do tc <- headof tcl (msg "LustreVGen.trans_expr: ApplyExprT: prefixL_binary");
      let tc' := typeof_binop binop tc in
      OK (g, Eprefix binop els tc')
    end
  | IteratorT highorder subop i =>
    match subop with 
    | LustreW.Nodehandler id nk rts =>
      let (isid, g1) := gencall g in
      let num := Int.unsigned i in 
      let c := mkcalldef nk isid id (Some i) xH Cltypes.Fnil nil nil in
      match highorder with
      | Omap =>
        let ck := match tcl with
            | nil => global_clock
            | (ty,ck) :: tl => ck
            end in
        let tcl1 := map (fun ty => (Tarray xH (trans_type ty) num, ck)) rts in
        let (g2, tcl') := register_typeclocks tcl1 g1 in
        OK (g2, Efor true (Oiteratorcall highorder c) i els tcl')  
      | Ofill | Ored | Ofillred => 
        match tcl, rts with
        | (_, ck)::tl, rty:: rtl =>
          let tcl1 := (trans_type rty, ck) :: map (fun ty => (Tarray xH (trans_type ty) num, ck)) rtl in
          let (g2, tcl') := register_typeclocks tcl1 g1 in
          OK (g2, Efor true (Oiteratorcall highorder c) i els tcl')  
        | _, _ =>  Error (msg "LustreVGen.trans_expr: ApplyExprT: fill red fillred: call")
        end 
      end 
    | LustreW.PrefixL_unary unop => 
      match highorder with
      | Omap => 
        do (ty, ck) <- headof tcl (msg "LustreVGen.trans_expr: ApplyExprT: iteratorT: map: prefixL_unary");
        match ty with 
        | Tarray id aty num => 
          let (aty',_) := typeof_unop unop (aty,ck) in
          let (g1, ty') := register_type g (Tarray xH aty' num) in
          OK (g1, Efor true (Omapunary unop) i els ((ty', ck)::nil))
        | _ => Error (msg "LustreVGen.trans_expr: ApplyExprT: iteratorT: map: prefixL_unary")
        end
      | Ored | Ofill | Ofillred =>
        do tc <- headof tcl (msg "LustreVGen.trans_expr: ApplyExprT: fillred: prefixL_unary");
        let tc' := typeof_unop unop tc in  
        OK (g, Efor true (Ofoldunary unop) i els (tc'::nil))
      end
    | LustreW.PrefixL_binary binop => 
      match highorder with
      | Omap =>
        match tcl with
        | tc1::(Tarray id aty num, ck)::_ =>
          let (aty',_) := typeof_binop binop (aty,ck) in
          let (g1, ty') := register_type g (Tarray xH aty' num) in
          match classify_binop aty binop with
          | binop_case_typecmp cmp =>
            OK (g1, Efor true (Omaptycmp cmp) i els ((ty', ck)::nil))
          | binop_case_normal => 
            OK (g1, Efor true (Omapary binop) i els ((ty', ck)::nil))
          end
        | _ => Error (msg "LustreVGen.trans_expr: ApplyExprT: iteratorT: map: prefixL_binary")
        end   
      | Ored | Ofill | Ofillred =>
        match tcl with
        | tc1::tc2::_ => 
          OK (g, Efor true (Ofoldary binop) i els (tc1::nil))
        | _ => Error (msg "LustreVGen.trans_expr: ApplyExprT: fillred: prefixL_binary")
        end	  
      end
    end
  end.

Fixpoint register_var_decls(vs: LustreW.vars)(g: generator) : (generator*vars) :=
  match vs with
  | nil => (g, nil)
  | (id, ty, ck) :: vtl =>
    let (g1, ty1) := register_type g (trans_type ty) in
    let (g2, vtl1) := register_var_decls vtl g1 in
    (g2, ((id, ty1, ck) :: vtl1))
  end. 

Fixpoint trans_equation_list(eqs: list equationT) (g: generator): res (generator*(list equation)) :=
  match eqs with
  | nil => OK (g, nil)
  | EquationT lh_list exp ::tl =>
    do (g1, exp1) <- trans_expr exp g;
    let (g2, lhs) := register_var_decls lh_list g1 in
    do (g3, eqs2) <- trans_equation_list tl g2;
    OK (g3, Equation lhs exp1 :: eqs2)
  end.

Definition trans_node(nod: nodeT)(g: generator): res (generator*(ident*node)) :=
  match nod with
  | NodeT kind id param rets vl eqs =>
    let (g1, param') := register_var_decls param g in
    let (g2, rets') := register_var_decls rets g1 in
    let (g3, vl') := register_var_decls vl g2 in
    do (g4, eqs2) <- trans_equation_list eqs g3;
    OK (g4, (id, mknode kind param' rets' vl' eqs2))
  end.

Fixpoint trans_nodes(nodes: list nodeT)(g: generator): res (generator*(list (ident*node))) :=
  match nodes with
  | nil => OK (g,nil)
  | hd::tl => 
    do (g1, f) <- trans_node hd g;
    let g2 := mkgenerator (struct_next g1) (array_next g1) xH xH (type_trail g1) in
    do (g3, fl) <- trans_nodes tl g2;
    OK (g3, f::fl)
  end.

Fixpoint register_constblock(l: list (ident*typeL*constL))(g: generator) : (generator*list (ident*type*constL)) :=
  match l with
  | nil => (g, nil)
  | (id, ty, v) :: tl =>
    let (g1, ty1) := register_type g (trans_type ty) in
    let (g2, tl') := register_constblock tl g1 in
    (g2, ((id, ty1, v) :: tl'))
  end. 

Fixpoint register_typeblock(l: list (ident*typeL))(g: generator) :  generator :=
  match l with
  | nil => g
  | (id, ty) :: tl =>
    let (g1, ty1) := register_globaltype id g (trans_type ty) in
    register_typeblock tl g1
  end. 

Fixpoint trans_const(item : constL)  : list AST.init_data :=
  match item with
  | ShortConstL i => AST.Init_int16 i :: nil
  | UshortConstL i => AST.Init_int16 i :: nil
  | IntConstL i => AST.Init_int32 i :: nil
  | UintConstL i => AST.Init_int32 i :: nil
  | CharConstL c => AST.Init_int8 c :: nil
  | BoolConstL b => AST.Init_int8 (trans_bool b) :: nil
  | RealConstL r => AST.Init_float64 r :: nil
  | FloatConstL r => AST.Init_float32 r :: nil
  | ID id => Init_addrof id Int.zero :: nil
  | ConstructConstL csl => trans_const_list csl
  end 

with trans_const_list(const_list: const_listL) : list AST.init_data :=
  match const_list with
  | ConstNilL => nil
  | ConstConL l_item rest =>
    let l_item' := trans_const l_item in
    let rest' := trans_const_list rest in
    l_item' ++ rest'
  end.

Definition trans_const_block(c: ident*type*constL) : ident* globvar type :=
  match c with
  | (id, ty, v) =>
    let v' := trans_const v in
    (id, (mkglobvar ty v' true true))
  end.

Definition trans_program (p: programT) : res program :=
  let g := mkgenerator xH xH xH xH nil in
  let g1 := register_typeblock (type_blockT p) g in
  let (g2, consts) := register_constblock (const_blockT p) g1 in
  let consts' := map trans_const_block consts in
  do (g', nodes) <- trans_nodes p.(node_blockT) g2;
  OK (mkprogram (type_trail g') consts' nodes p.(node_mainT)).

Scheme exprs_ind2 :=
  Induction for exprT Sort Prop
with expr_lists_ind2 :=
  Induction for expr_listT Sort Prop
with struct_lists_ind2 :=
  Induction for struct_listT Sort Prop
with pattern_lists_ind2 :=
  Induction for pattern_listT Sort Prop
with label_index_list_ind2 :=
  Induction for label_index_listT Sort Prop
with operator_ind2 :=
  Induction for operatorT Sort Prop.

Scheme exprs_ind3 := Minimality for exprT Sort Prop
  with expr_lists_ind3 := Minimality for expr_listT Sort Prop
  with struct_lists_ind3 := Minimality for struct_listT Sort Prop
  with pattern_lists_ind3 := Minimality for pattern_listT Sort Prop
  with label_lindex_lists_ind3 := Minimality for label_index_listT Sort Prop
  with operator_ind3 := Minimality for operatorT Sort Prop.  