Require Import AST.
Require Import Coqlib.
Require Import String.
(* AST *)
Definition str := string.
Record ident := { name: str; key: BinNums.positive }.

Inductive singleclock : Type :=
  | Clock : bool -> ident -> singleclock
  | NOCLOCK : singleclock.

Inductive funcType : Type :=
  | Function: funcType
  | Node: funcType.

Inductive atomType : Type :=
  | Bool : atomType
  | Int : atomType
  | Real : atomType.

Inductive unOp : Type :=
  | NOT : unOp
  | POS : unOp
  | NEG : unOp.

Inductive binOp : Type :=
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

Inductive atomExpr : Type :=
  | EIdent : ident -> atomExpr
  | EBool : ident -> atomExpr
  | EInt : ident -> atomExpr
  | EReal : ident -> atomExpr.

Inductive constExpr : Type :=
  | CEAtom: atomExpr -> constExpr
  | CEUnOpExpr : unOp -> constExpr -> constExpr
  | CEBinOpExpr : binOp -> constExpr -> constExpr -> constExpr
  | CEConstructor: cNameItems -> constExpr
  | CEArray: constExprlist -> constExpr
with constExprlist : Type :=
  | CEnil : constExprlist
  | CEcons : constExpr -> constExprlist -> constExprlist
with cNameItems : Type :=
  | CNamesNil : cNameItems
  | CNamesCons: ident -> constExpr -> cNameItems -> cNameItems.

Inductive kind : Type :=
  | AtomType : atomType -> kind 
  | Struct : fieldlist -> kind
  | Array : kind -> constExpr -> kind
  | EnumType : list ident -> kind
  | TypeDef: ident -> kind
with fieldlist : Type :=
  | Fnil : fieldlist
  | Fcons : ident -> kind -> fieldlist -> fieldlist.

Inductive mega : Type :=
  | Mega : ident -> ident -> mega.

Inductive expr : Type :=
  | AtomExpr : atomExpr -> expr
  | UnOpExpr : unOp -> expr -> expr
  | BinOpExpr : binOp -> expr -> expr -> expr
  | FieldExpr : expr -> ident -> expr
  | ArrAccessExpr : expr -> constExpr -> expr
  | ArrInitExpr : expr -> constExpr -> expr
  | ArrConstructExpr : exprlist -> expr
  | NameConstructExpr : namelist -> expr
  | PreExpr : expr -> expr
  | FbyExpr : exprlist -> constExpr -> exprlist -> expr
  | ArrowExpr : expr -> expr -> expr
  | WhenExpr : expr -> bool -> ident -> expr
  | CurrentExpr : expr -> expr
  | IfExpr : expr -> expr -> expr -> expr
  | ExprList : exprlist -> expr
  | Call : ident -> exprlist -> expr
  | DieseExpr : expr -> expr
  | NorExpr : expr -> expr
  | MergeExpr : ident -> expr -> expr -> expr

with exprlist : Type :=
  | Enil : exprlist
  | Econs : expr -> exprlist -> exprlist 

with namelist : Type :=
  | NamesNil : namelist
  | NamesCons : ident -> expr -> namelist -> namelist.

Inductive lhs : Type :=
  | LVIdent : list ident -> lhs
  | LVMega : mega -> lhs.

Inductive rhs : Type :=
  | RVExpr : expr -> rhs
  | RVMega : mega -> rhs.

Inductive eqStmt : Type :=
  | EqStmt : lhs -> rhs -> eqStmt.

Inductive varBlk : Type :=
  | VarList : list (ident * kind * singleclock) -> varBlk.

Inductive paramBlk : Type :=
  | ParamBlk : list (ident * kind * singleclock) -> paramBlk.

Inductive staticBlk : Type :=
  | StaticBlk : list (ident * kind) -> staticBlk.

Inductive returnBlk : Type :=
  | ReturnBlk : list (ident * kind * singleclock) -> returnBlk.

Inductive bodyBlk : Type :=
  | BodyBlk : varBlk -> list eqStmt -> bodyBlk.

Inductive typeStmt : Type :=
  | TypeStmt : ident -> kind -> typeStmt.

Inductive constStmt : Type :=
  | ConstStmt : ident -> kind -> constExpr -> constStmt.

Inductive nodeBlk : Type :=
  | TypeBlk : list typeStmt -> nodeBlk
  | ConstBlk : list constStmt -> nodeBlk
  | FuncBlk : funcType -> ident -> paramBlk -> returnBlk -> bodyBlk -> nodeBlk
  | WidgetBlk : ident -> staticBlk -> paramBlk -> returnBlk -> nodeBlk
  | ControlBlk : ident -> bodyBlk -> nodeBlk.

Inductive program : Type :=
  | Program : list nodeBlk -> program.
