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

Require Import BinNums.
Require Import Coqlib.
Require Import String.

(* Lustre* AST definition *)

Definition str := string.
Record ident := { name: str; key: BinNums.positive }.
Definition integer := str.

Inductive singleclock :=
  | Clock : bool -> ident -> singleclock
  | NOCLOCK : singleclock.

Inductive funcType :=
  | Function: funcType
  | Node: funcType.

Inductive atomType :=
  | Bool : atomType
  | Short : atomType
  | UShort : atomType
  | Int : atomType
  | UInt : atomType
  | Float : atomType
  | Real : atomType
  | Char : atomType.

Inductive unOp :=
  | AtomTypeOp : atomType -> unOp
  | NOT : unOp
  | POS : unOp
  | NEG : unOp.

Inductive binOp :=
  | ADD : binOp
  | SUB : binOp
  | MUL : binOp
  | DIVF : binOp
  | DIV : binOp
  | MOD : binOp
  | AND : binOp
  | OR : binOp
  | XOR : binOp
  | GT : binOp
  | LT : binOp
  | GE : binOp
  | LE : binOp
  | EQ : binOp
  | NE : binOp.

Inductive prefixUnOp :=
  | PSHORT : prefixUnOp
  | PINT : prefixUnOp
  | PFLOAT : prefixUnOp
  | PREAL : prefixUnOp
  | PNOT : prefixUnOp
  | PPOS : prefixUnOp
  | PNEG : prefixUnOp.

Inductive highOrderOp :=
  | MAP : highOrderOp
  | RED : highOrderOp
  | FILL : highOrderOp
  | FILLRED : highOrderOp.

Inductive prefixOp :=
  | Ident : ident -> prefixOp
  | UnOp : prefixUnOp -> prefixOp
  | BinOp : binOp -> prefixOp.

Inductive atomExpr :=
  | EIdent : ident -> atomExpr
  | EBool : ident -> atomExpr
  | EChar : ident -> atomExpr
  | EShort : ident -> atomExpr
  | EUShort : ident -> atomExpr
  | EInt : ident -> atomExpr
  | EUInt : ident -> atomExpr
  | EFloat : ident -> atomExpr
  | EReal : ident -> atomExpr.

Inductive pattern :=
  | PIdent : ident -> pattern
  | PBool : ident -> pattern
  | PChar : ident -> pattern
  | PInt : ident -> pattern
  | DefaultPattern : pattern.

Inductive constExpr :=
  | CEAtom: atomExpr -> constExpr
  | CEUnOpExpr : unOp -> constExpr -> constExpr
  | CEBinOpExpr : binOp -> constExpr -> constExpr -> constExpr
  | CEConstructor: cNameItems -> constExpr
  | CEArray: constExprlist -> constExpr
with constExprlist :=
  | CEnil : constExprlist
  | CEcons : constExpr -> constExprlist -> constExprlist
with cNameItems :=
  | CNamesNil : cNameItems
  | CNamesCons: ident -> constExpr -> cNameItems -> cNameItems.

Inductive kind :=
  | AtomType : atomType -> kind 
  | Struct : fieldlist -> kind
  | Array : kind -> constExpr -> kind
  | EnumType : list ident -> kind
  | TypeDef: ident -> kind
with fieldlist :=
  | Fnil : fieldlist
  | Fcons : ident -> kind -> fieldlist -> fieldlist.

Inductive expr :=
  | AtomExpr : atomExpr -> expr
  | UnOpExpr : unOp -> expr -> expr
  | BinOpExpr : binOp -> expr -> expr -> expr
  | FieldExpr : expr -> ident -> expr
  | DynamicProjectExpr : expr -> exprlist -> expr -> expr
  | ArrAccessExpr : expr -> constExpr -> expr
  | ArrInitExpr : expr -> constExpr -> expr
  | ArrConstructExpr : exprlist -> expr
  | NameConstructExpr : namelist -> expr
  | PreExpr : expr -> expr
  | FbyExpr : exprlist -> constExpr -> exprlist -> expr
  | ArrowExpr : expr -> expr -> expr
  | WhenExpr : expr -> bool -> ident -> expr
  | CurrentExpr : expr -> expr
  | MergeExpr : ident -> expr -> expr -> expr
  | IfExpr : expr -> expr -> expr -> expr
  | CaseExpr : expr -> caselist-> expr
  | NameWithExpr : ident -> withlist -> expr -> expr
  | ExprList : exprlist -> expr
  | PrefixExpr : prefixOp -> exprlist -> expr
  | HighOrderExpr : highOrderOp -> prefixOp -> constExpr -> exprlist -> expr
  | BoolredExpr : integer -> integer -> expr -> expr
  | DieseExpr : expr -> expr
  | NorExpr : expr -> expr

with exprlist :=
  | Enil : exprlist
  | Econs : expr -> exprlist -> exprlist 

with caselist :=
  | CasesNil : caselist
  | CasesCons : pattern -> expr -> caselist -> caselist

with namelist :=
  | NamesNil : namelist
  | NamesCons : ident -> expr -> namelist -> namelist

with withitem :=
  | FieldItem : ident -> withitem
  | AccessItem : expr -> withitem

with withlist :=
  | WithNil : withlist
  | WithCons : withitem -> withlist -> withlist.

Inductive eqStmt :=
  | EqStmt : list ident -> expr -> eqStmt.

Inductive varBlk :=
  | VarList : list (ident*kind*singleclock) -> varBlk
  | NOVARBLK.

Inductive paramBlk :=
  | ParamBlk : list (ident*kind*singleclock) -> paramBlk.

Inductive returnBlk :=
  | ReturnBlk :  list (ident*kind*singleclock) -> returnBlk.

Inductive bodyBlk :=
  | BodyBlk : varBlk -> list eqStmt -> bodyBlk.

Inductive typeStmt :=
  | TypeStmt : ident -> kind -> typeStmt.

Inductive constStmt :=
  | ConstStmt : ident -> kind -> constExpr -> constStmt.

Inductive nodeBlk :=
  | TypeBlk : list typeStmt -> nodeBlk
  | ConstBlk : list constStmt -> nodeBlk
  | FuncBlk : funcType -> ident -> paramBlk -> returnBlk -> bodyBlk -> nodeBlk.

Inductive program :=
  | Program : list nodeBlk -> program.

