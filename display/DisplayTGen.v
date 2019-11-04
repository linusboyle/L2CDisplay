Require Import AST.
Require Import Coqlib.
Require Import DisplayT.
Require Import Errors.
Require Import GTree.
Require Import Maps.
Require Import Ctypes.
Require Import Cltypes.
Require Import String.
Require Import Ascii.
Require Import Integers.

Definition err_nd_notfound {A : Type} (ndname : ident) : res A :=
  Error ((MSG "Node ") :: (CTX ndname) :: (MSG " not found" :: nil)).

Definition err_sl_notfound {A : Type} (slname : ident) : res A :=
  Error ((MSG "Paramemter ") :: (CTX slname) :: (MSG " not found" :: nil)).

Definition err_ty_incompatible {A : Type} : res A :=
  Error (msg "Type not compatible").

Definition acg_const_name(id: ident) :=   (**r acg_const<num>*)
  Lident.intern_string (String.append ("acg_const") (Lident.string_of_positive id)).

Definition acg_const_str_name (id: ident) :=
  Lident.intern_string (String.append ("__stringlit_") (Lident.string_of_positive id)).

Definition add_node (ne: nodeenv) (nd : ident * LustreS.node) :=
  PTree.set (fst nd) (snd nd) ne.

Record generator : Type := mkgenerator {
  const_next : ident;
  node_env : nodeenv;
  const_env : constenv
}.

Fixpoint register_node (ne: nodeenv) (nodes : list (ident * LustreS.node)) :=
  match nodes with
  | nil => ne
  | nhd :: ntl =>
      let ne1 := add_node ne nhd in
      register_node ne1 ntl
  end.

Fixpoint check_slot (varlist: list(ident*type)) (slname: ident) : option type :=
  match varlist with 
  | nil => None
  | (vi, vt) :: tl => if peq slname vi then Some vt
                      else check_slot tl slname
  end.

(* IDEA: https://stackoverflow.com/a/15537644/9552755 *)
Definition Z_of_bool (b : bool) := if b then 1 else 0.

Coercion Z_of_bool : bool >-> Z.

Definition Z_of_ascii a :=
  match a with
   Ascii b1 b2 b3 b4 b5 b6 b7 b8 =>
     b1 + 2 * (b2 + 2 * (b3 + 2 * (b4 + 2 *
      (b5 + 2 * (b6 + 2 * (b7 + 2 * b8))))))
  end.

Fixpoint trans_str (str: string) :=
  match str with
  | String.EmptyString => nil
  | String.String hc ts => 
    let h' := Init_int8 (Int.repr (Z_of_ascii hc)) in
    let t' := trans_str ts in
    h' :: t'
  end.

Definition trans_constval (cv: constG) : type * list init_data :=
  match cv with
  | GBool b => (type_bool, Init_int8 (Lustre.trans_bool b) :: nil)
  | GChar c => (Tint I8 Signed, Init_int8 c :: nil)
  | GShort i => (Tint I16 Signed, Init_int16 i :: nil)
  | GUShort i => (Tint I16 Unsigned, Init_int16 i :: nil)
  | GInt i => (Tint I32 Signed, Init_int32 i :: nil)
  | GUInt i => (Tint I32 Unsigned, Init_int32 i :: nil)
  | GFloat r => (Tfloat F32, Init_float32 r :: nil)
  | GReal r => (Tfloat F64, Init_float64 r :: nil)
  | GString id => (Tpointer (Tint I8 Signed), trans_str (Lident.extern_atom id))
  end.

Definition trans_const (cv: constG) :=
  let (ty, v') := trans_constval cv in
  mkglobvar ty v' true true.

Local Open Scope error_monad_scope.

Fixpoint trans_slot (ge: generator) (attr: attribute) : res (generator * slot) :=
  match attr with
  | SConst na cv =>
      let var := trans_const cv in
      let cid := 
        match cv with
        | GString _ => acg_const_str_name (const_next ge)
        | _ => acg_const_name (const_next ge)
        end 
      in
      let ce1 := PTree.set cid var (const_env ge) in
      let gen1 := mkgenerator (Psucc (const_next ge)) (node_env ge) ce1 in
      OK (gen1, TConst na cid)
  | SNodeRef name nd sl => 
      let ne := node_env ge in
      match ne ! nd with
      | None => err_nd_notfound nd
      | Some node =>
          let args := Lustre.nd_args node in
          let rets := Lustre.nd_rets node in
          match check_slot args sl with
          | Some ty => OK (ge, TRefin name nd sl ty)
          | None =>
              match check_slot rets sl with
              | Some ty1 => OK (ge, TRefout name nd sl ty1)
              | None => err_sl_notfound sl
              end
          end
      end
  end.

Fixpoint trans_slots (ge: generator) (attrs: list attribute) : res (generator * list slot) :=
  match attrs with
  | nil => OK (ge, nil)
  | ha :: ta =>
      do (ge1, hs) <- trans_slot ge ha;
      do (ge2, ts) <- trans_slots ge1 ta;
      OK (ge2, hs :: ts)
  end.

Fixpoint trans_node (ge: generator) (tree: GTree) : res (generator * displayT) :=
  match tree with
  | GNode id subnodes attrs =>
      do (ge1, subt) <- trans_nodes ge subnodes;
      do (ge2, sls) <- trans_slots ge1 attrs;
      OK (ge2, TNode id subt sls)
  end
with trans_nodes (ge: generator) (nds: treeList) : res (generator * displayList) :=
  match nds with
  | GNil => OK (ge, TNil)
  | GCons hnd tnds =>
      do (ge1, hdis) <- trans_node ge hnd;
      do (ge2, tdis) <- trans_nodes ge1 tnds;
      OK (ge2, TCons hdis tdis)
  end.

Definition trans_model (tree: GTree) (program: LustreS.program) : res modelT :=
  let ne := register_node empty_nodeenv (Lustre.node_block program) in
  let ge := mkgenerator xH ne empty_constenv in
  do (ge1, model) <- trans_node ge tree;
  OK (mkmodelT model (const_env ge1) (node_env ge1)).
