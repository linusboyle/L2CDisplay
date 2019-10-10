// Project:  Open L2C
// File:     Parser.vy
// Author:   Ling Li
// Date:     2018.04.08

%{

Require Import BinNums.
Require Import Tree.
Require Import String.
Require Import List.

Open Scope string_scope.

Parameter intern_string: String.string -> positive.
Parameter ocaml_string: String.string -> integer.

Fixpoint cons_fieldlist (l : list (ident * kind)) : fieldlist :=
  match l with
    | nil => 
      Fnil
    | (v1, v2) :: other => 
      Fcons v1 v2 (cons_fieldlist other)
  end.

Fixpoint cons_constexprlist (l : list constExpr) : constExprlist :=
  match l with
    | nil =>
      CEnil
    | v1 :: other =>
      CEcons v1 (cons_constexprlist other)
  end.

Fixpoint cons_conststructlist (l : list (ident * constExpr)) : cNameItems :=
  match l with
    | nil =>
      CNamesNil
    | (v1, v2) :: other =>
      CNamesCons v1 v2 (cons_conststructlist other)
  end.

Fixpoint cons_exprlist (l : list expr) : exprlist :=
  match l with
    | nil =>
      Enil
    | v1 :: other =>
      Econs v1 (cons_exprlist other)
  end.

Fixpoint cons_caselist (l : list (pattern * expr)) : caselist :=
  match l with
    | nil =>
      CasesNil
    | (v1, v2) :: other =>
      CasesCons v1 v2 (cons_caselist other)
  end.

Fixpoint cons_namelist (l : list (ident *expr)) : namelist :=
  match l with
    | nil =>
      NamesNil
    | (v1, v2) :: other =>
      NamesCons v1 v2 (cons_namelist other)
  end.

Fixpoint cons_withlist (l : list withitem) : withlist :=
  match l with
    | nil =>
      WithNil
    | v1 :: other =>
      WithCons v1 (cons_withlist other)
  end.

%}

%token TYPE CONST FUNCTION NODE VAR RETURNS LET TEL ENUM
%token PRE FBY IF THEN ELSE WHEN CASE OF DEFAULTPATTERN ARROW SEG WITH MERGE CURRENT
%token SHORTSSS INTSSS FLOATSSS REALSSS NOTSSS ADDSSS MINUSSSS
%token SSSADDSSS SSSMINUSSSS SSSMULSSS SSSDIVFSSS SSSDIVSSS SSSMODSSS SSSANDSSS SSSORSSS SSSXORSSS
%token SSSEQSSS SSSNESSS SSSGRESSS SSSGREEQSSS SSSLESSSS SSSLESEQSSS
%token MAP RED FILL FILLRED BOOLRED DIESE NOR DEFAULT
%token CHAR BOOL SHORT USHORT INT UINT FLOAT REAL

%token NOT ADD MINUS MUL DIVF DIV MOD AND OR XOR LESEQ GREEQ NE EQ LES GRE

%token<string> TRUE FALSE
%token<string> IDENT CONST_USHORT CONST_SHORT CONST_UINT CONST_INT CONST_FLOAT CONST_REAL CONST_CHAR

%token LPAREN RPAREN LBRACKET RBRACKET LBRACE RBRACE
%token COMMA COLON SEMICOLON CARET  DOT

%token EOF

%type<list nodeBlk> p_Block_List
%type<nodeBlk> p_Block
%type<nodeBlk> p_Type_Block
%type<list typeStmt> p_Type_Statement_List
%type<typeStmt> p_Type_Statement
%type<kind> p_Kind
%type<list (ident * kind)> p_Field_List
%type<list (ident * kind)> p_Field
%type<list ident> p_Ident_List
%type<atomType> p_Atom_Type
%type<nodeBlk> p_Const_Block
%type<list constStmt> p_Const_Statement_List
%type<constStmt> p_Const_Statement
%type<constExpr> p_Const_Expression
%type<list constExpr> p_Const_Expression_List
%type<list (ident * constExpr)> p_Const_Field_List
%type<list (ident * constExpr)> p_Const_Field
%type<constExpr> p_Const_Binary_Expression
%type<constExpr> p_Const_Or_Expression
%type<constExpr> p_Const_And_Expression
%type<constExpr> p_Const_Compare_Expression
%type<constExpr> p_Const_Not_Expression
%type<constExpr> p_Const_Additive_Expression
%type<constExpr> p_Const_Multiplicative_Expression
%type<constExpr> p_Const_Unary_Expression
%type<constExpr> p_Const_Primary_Expression
%type<atomExpr> p_Atom_Expression
%type<nodeBlk> p_Function_Block
%type<funcType> p_Function_Type
%type<paramBlk> p_Parameter_Block
%type<returnBlk> p_Return_Block
%type<list (ident * kind * singleclock)> p_Variable_List
%type<list (ident * kind * singleclock)> p_Variable
%type<bodyBlk> p_Body_Block
%type<varBlk> p_Variable_Block
%type<list eqStmt> p_Equation_List
%type<eqStmt> p_Equation
%type<list ident> p_Lefthand_List
%type<ident> p_Lefthand
%type<expr> p_Simple_Fby_Expression
%type<expr> p_Expression
%type<expr> p_Calculative_Expression
%type<expr> p_If_Expression
%type<expr> p_Arrow_Expression
%type<expr> p_Or_Expression
%type<expr> p_And_Expression
%type<expr> p_Compare_Expression
%type<expr> p_Not_Expression
%type<expr> p_Additive_Expression
%type<expr> p_Multiplicative_Expression
%type<expr> p_When_Expression
%type<expr> p_Unary_Expression
%type<expr> p_Nary_Expression
%type<expr> p_Access_Expression
%type<list expr> p_Projection_Index_List
%type<expr> p_Projection_Index
%type<expr> p_Primary_Expression
%type<list expr> p_Expression_List
%type<list expr> p_Nonempty_Expression_List
%type<expr> p_Case_Expression
%type<list (pattern * expr)> p_Pattern_Expression_List
%type<(pattern * expr)> p_Pattern_Expression
%type<pattern> p_Pattern
%type<expr> p_Struct_Construct_Expression
%type<list (ident * expr)> p_Struct_Field_List
%type<(ident * expr)> p_Struct_Field
%type<expr> p_Array_Construct_Expression
%type<expr> p_With_Construct_Expression
%type<list withitem> p_Label_Index_List
%type<withitem> p_Label_Index
%type<expr> p_Prefix_Expression
%type<prefixOp> p_Prefix_Operator
%type<prefixUnOp> p_Prefix_Unary_Operator
%type<binOp> p_Prefix_Binary_Operator
%type<expr> p_High_Order_Expression
%type<highOrderOp> p_High_Order_Operator
%type<expr> p_Tempo_Expression
%type<expr> p_Merge_Expression
%type<integer> p_Const_Integer

%start<program> p_Program
%%

(* 1.1. Program.program *)
p_Program:
  | v1 = p_Block_List; EOF
    { Program v1 }
  ;

p_Block_List:
  | v1 = p_Block; v2 = p_Block_List
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* 1.2. Program.decls *)
p_Block:
  | v1 = p_Type_Block
    { v1 }
  | v1 = p_Const_Block
    { v1 }
  | function_block = p_Function_Block
    { function_block }
  ;

(* 2.1. TypeBlock.type_decl *)
p_Type_Block:
  | TYPE; v1 = p_Type_Statement_List
    { TypeBlk v1 }
  ;

(* 2.2. TypeBlock.type_decl_list *)
p_Type_Statement_List:
  | v1 = p_Type_Statement; SEMICOLON; v2 = p_Type_Statement_List;
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* 2.3. TypeBlock.one_type_decl *)
p_Type_Statement:
  | v1 = IDENT; EQ; v2 = p_Kind
    { TypeStmt {| name := v1; key := intern_string v1 |} v2 }
  ;

(* 2.4. TypeBlock.kind *)
p_Kind:
  | v1 = IDENT
    { TypeDef {| name := v1; key := intern_string v1 |} }
  | v1 = p_Atom_Type
    { AtomType v1 }
  | v1 = p_Kind; CARET; v2 = p_Const_Additive_Expression
    { Array v1 v2 }
  | LBRACE; v1 = p_Field_List; RBRACE
    { Struct (cons_fieldlist v1) }
  | ENUM; LBRACE; v1 = p_Ident_List; RBRACE
    { EnumType v1 }
  ;

p_Atom_Type:
  |	BOOL
    { Bool }
  |	SHORT
    { Short }
  |	USHORT
    { UShort }
  |	INT
    { Int }
	|	UINT
    { UInt }
  |	FLOAT	
    { Float }
	|	REAL
    { Real }
  | CHAR
    { Char }
  ;

p_Ident_List:
  | v1 = IDENT; COMMA; v2 = p_Ident_List
    { {| name := v1; key := intern_string v1 |} :: v2 }
  | v1 = IDENT
    { [{| name := v1; key := intern_string v1 |}] }
  ;

(* 2.5. TypeBlock.field_decl *)
p_Field_List:
  | v1 = p_Field; COMMA; v2 = p_Field_List
    { v1 ++ v2 }
  | v1 = p_Field
    { v1 }
  ;

p_Field:
  | v1 = p_Ident_List; COLON; v2 = p_Kind
    { List.map (fun i => (i, v2)) v1 }
  ;

(* 3.1. ConstBlock.const_decl *)
p_Const_Block:
  | CONST; v1 = p_Const_Statement_List
    { ConstBlk v1 }
  ;

(* 3.2. ConstBlock.const_decl_list *)
p_Const_Statement_List:
  | v1 = p_Const_Statement; SEMICOLON; v2 = p_Const_Statement_List;
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* 3.3. ConstBlock.one_const_decl *)
p_Const_Statement:
  | v1 = IDENT; COLON; v2 = p_Kind; EQ; v3 = p_Const_Expression
    { ConstStmt {| name := v1; key := intern_string v1 |} v2 v3 }
  ;

(* 3.4. ConstBlock.const_expr *)
p_Const_Expression:
  | v1 = p_Const_Binary_Expression
    { v1 }
  | LBRACKET; v1 = p_Const_Expression_List; RBRACKET
    { CEArray (cons_constexprlist v1) }
  | LBRACE; v1 = p_Const_Field_List; RBRACE
    { CEConstructor (cons_conststructlist v1) }
//  | ENUM; LPAREN; v1 = IDENT; COMMA; kind = p_Kind; RPAREN
//    { CEEnum {| name := v1; key := intern_string v1 |} kind }
  ;

p_Const_Expression_List:
  | v1 = p_Const_Expression; COMMA; v2 = p_Const_Expression_List
    { v1 :: v2 }
  | v1 = p_Const_Expression
    { [v1] }
  ;

(* 3.6. ConstBlock.field_const *)
p_Const_Field_List:
  | v1 = p_Const_Field; COMMA; v2 = p_Const_Field_List
    { v1 ++ v2 }
  | v1 = p_Const_Field
    { v1 }
  ;

p_Const_Field:
  | v1 = p_Ident_List; COLON; v2 = p_Const_Expression
    { List.map (fun i => (i, v2)) v1 }
  ;

p_Const_Binary_Expression:
  | v1 = p_Const_Or_Expression
    { v1 }
  ;

p_Const_Or_Expression:
  | v1 = p_Const_And_Expression
    { v1 }
  | v1 = p_Const_Or_Expression; OR; v2 = p_Const_And_Expression
    { CEBinOpExpr OR v1 v2 }
  | v1 = p_Const_Or_Expression; XOR; v2 = p_Const_And_Expression
    { CEBinOpExpr XOR v1 v2 }
  ;

p_Const_And_Expression:
  | v1 = p_Const_Compare_Expression
    { v1 }
  | v1 = p_Const_And_Expression; AND; v2 = p_Const_Compare_Expression
    { CEBinOpExpr AND v1 v2 }
  ;

p_Const_Compare_Expression:
  | v1 = p_Const_Not_Expression
    { v1 }
  | v1 = p_Const_Compare_Expression; LES; v2 = p_Const_Not_Expression
    { CEBinOpExpr LT v1 v2 }
  | v1 = p_Const_Compare_Expression; GRE; v2 = p_Const_Not_Expression
    { CEBinOpExpr GT v1 v2 }
  | v1 = p_Const_Compare_Expression; GREEQ; v2 = p_Const_Not_Expression
    { CEBinOpExpr GE v1 v2 }
  | v1 = p_Const_Compare_Expression; LESEQ; v2 = p_Const_Not_Expression
    { CEBinOpExpr LE v1 v2 }
  | v1 = p_Const_Compare_Expression; NE; v2 = p_Const_Not_Expression
    { CEBinOpExpr NE v1 v2 }
  | v1 = p_Const_Compare_Expression; EQ; v2 = p_Const_Not_Expression
    { CEBinOpExpr EQ v1 v2 }
  ;

p_Const_Not_Expression:
  | v1 = p_Const_Additive_Expression
    { v1 }
  | NOT; v1 = p_Const_Not_Expression
    { CEUnOpExpr NOT v1 }
  ;

p_Const_Additive_Expression:
  | v1 = p_Const_Multiplicative_Expression
    { v1 }
  | v1 = p_Const_Additive_Expression; ADD; v2 = p_Const_Multiplicative_Expression
    { CEBinOpExpr ADD v1 v2 }
  | v1 = p_Const_Additive_Expression; MINUS; v2 = p_Const_Multiplicative_Expression
    { CEBinOpExpr SUB v1 v2 }
  ;

p_Const_Multiplicative_Expression:
  | v1 = p_Const_Unary_Expression
    { v1 }
  | v1 = p_Const_Multiplicative_Expression; MUL; v2 = p_Const_Unary_Expression
    { CEBinOpExpr MUL v1 v2 }
  | v1 = p_Const_Multiplicative_Expression; DIVF; v2 = p_Const_Unary_Expression
    { CEBinOpExpr DIVF v1 v2 }
  | v1 = p_Const_Multiplicative_Expression; DIV; v2 = p_Const_Unary_Expression
    { CEBinOpExpr DIV v1 v2 }
  | v1 = p_Const_Multiplicative_Expression; MOD; v2 = p_Const_Unary_Expression
    { CEBinOpExpr MOD v1 v2 }
  ;

p_Const_Unary_Expression:
  | v1 = p_Const_Primary_Expression
    { v1 }
  | ADD; v1 = p_Const_Unary_Expression
    { CEUnOpExpr POS v1 }
  | MINUS; v1 = p_Const_Unary_Expression
    { CEUnOpExpr NEG v1 }
  ;

p_Const_Primary_Expression:
  | v1 = p_Atom_Expression
    { CEAtom v1 }
  | LPAREN; v1 = p_Const_Expression; RPAREN
    { v1 }
  ;

(* 3.5. ConstBlock.atom *)
p_Atom_Expression:
  | v1 = IDENT
    { EIdent {| name := v1; key := intern_string v1 |} }
  | v1 = TRUE
    { EBool {| name := v1; key := xH |} }
  | v1 = FALSE
    { EBool {| name := v1; key := xH |} }
  | v1 = CONST_INT
    { EInt {| name := v1; key := xH |}  }
  | v1 = CONST_UINT
    { EUInt {| name := v1; key := xH |} }
  | v1 = CONST_SHORT
    { EShort {| name := v1; key := xH |} }
  | v1 = CONST_USHORT
    { EUShort {| name := v1; key := xH |} }
  | v1 = CONST_REAL
    { EReal {| name := v1; key := xH |} }
  | v1 = CONST_FLOAT
    { EFloat {| name := v1; key := xH |} }
  | v1 = CONST_CHAR
    { EChar {| name := v1; key := xH |} }
  ;

(* 4.1. NodeBlock.node_decl *)
p_Function_Block:
  | v1 = p_Function_Type; v2 = IDENT; v3 = p_Parameter_Block; v4 = p_Return_Block; v5 = p_Body_Block
    { FuncBlk v1 {| name := v2; key := intern_string v2 |} v3 v4 v5 }
  ;


(* 4.2. NodeBlock.func_type *)
p_Function_Type:
  | FUNCTION
    { Function }
  | NODE
    { Node }
  ;

(* 4.3. NodeBlock.decls *)
p_Parameter_Block:
  | LPAREN; v1 = p_Variable_List; RPAREN
    { ParamBlk v1 }
  ;

p_Return_Block:
  | RETURNS; LPAREN; v1 = p_Variable_List; RPAREN
    { ReturnBlk v1 }
  | RETURNS; LPAREN; v1 = p_Variable_List; RPAREN; SEMICOLON
    { ReturnBlk v1 }
  ;

p_Variable_List:
  | v1 = p_Variable; SEMICOLON; v2 = p_Variable_List
    { v1 ++ v2 }
  | v1 = p_Variable
    { v1 }
  | (* empty *)
    { [] }
  ;

(* 4.4. NodeBlock.var_decl *)
p_Variable:
  | v1 = p_Ident_List; COLON; v2 = p_Kind
    { List.map (fun i => ((i, v2), NOCLOCK)) v1 }
  | v1 = p_Ident_List; COLON; v2 = p_Kind; WHEN; v3 = IDENT
    { List.map (fun i => ((i, v2), Clock true {| name := v3; key := intern_string v3 |} )) v1 }
  | v1 = p_Ident_List; COLON; v2 = p_Kind; WHEN; NOT; v3 = IDENT
    { List.map (fun i => ((i, v2), Clock false {| name := v3; key := intern_string v3 |} )) v1 }
  | v1 = p_Ident_List; COLON; v2 = p_Kind; WHEN; NOT; LPAREN; v3 = IDENT; RPAREN
    { List.map (fun i => ((i, v2), Clock false {| name := v3; key := intern_string v3 |} )) v1 }
  ;

(* 4.6. NodeBlock.body *)
p_Body_Block:
  | v1 = p_Variable_Block; LET; v2 = p_Equation_List; TEL	
    { BodyBlk v1 v2 }
	|	v1 = p_Variable_Block; LET; v2 = p_Equation_List; TEL; SEMICOLON	
    { BodyBlk v1 v2 }
  ;

p_Variable_Block:
  | VAR v1 = p_Variable_List
    { VarList v1 }
	| (* empty *)
    { NOVARBLK }
  ;

(* 4.7. NodeBlock.equations *)
p_Equation_List:
  | v1 = p_Equation; v2 = p_Equation_List
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

(* 4.8. NodeBlock.equation *)
p_Equation:
  | v1 = p_Lefthand_List; EQ; v2 = p_Simple_Fby_Expression; SEMICOLON
    { EqStmt v1 v2 }
  ;

(* 4.9. NodeBlock.lhs *)
p_Lefthand_List:
  | v1 = p_Lefthand; COMMA; v2 = p_Lefthand_List
    { v1 :: v2 }
  | v1 = p_Lefthand
    { [v1] }
  | LPAREN; v1 = p_Lefthand_List; RPAREN
    { v1 }
  ;

(* 4.10. NodeBlock.lhs_id *)
p_Lefthand:
  | v1 = IDENT
    { {| name := v1; key := intern_string v1 |} }
  ;

(* 4.11. NodeBlock.expr *)
p_Simple_Fby_Expression:
  | v1 = p_Expression
    { v1 }
  | v1 = p_Nonempty_Expression_List; FBY; v2 = p_Nonempty_Expression_List
    { FbyExpr (cons_exprlist v2) (CEAtom ( EInt {| name := ocaml_string "1"; key := xH |} )) (cons_exprlist v1) }
  ;

p_Expression:
  | v1 = p_Calculative_Expression
    { v1 }
  ;

p_Calculative_Expression:
  | v1 = p_Arrow_Expression
    { v1 }
  ;
 
p_Arrow_Expression:
  | v1 = p_If_Expression
    { v1 }
  | v1 = p_Arrow_Expression; ARROW; v2 = p_If_Expression
    { ArrowExpr v1 v2 }
  ;

p_If_Expression:
  | v1 = p_Or_Expression
    { v1 }
  | IF; v1 = p_Expression ; THEN; v2 = p_Expression; ELSE; v3 = p_If_Expression
    { IfExpr v1 v2 v3 }
  ;

p_Or_Expression:
  | v1 = p_And_Expression
    { v1 }
  | v1 = p_Or_Expression; OR; v2 = p_And_Expression
    { BinOpExpr OR v1 v2 }
  | v1 = p_Or_Expression; XOR; v2 = p_And_Expression
    { BinOpExpr XOR v1 v2 }
  ;

p_And_Expression:
  | v1 = p_Compare_Expression
    { v1 }
  | v1 = p_And_Expression; AND; v2 = p_Compare_Expression
    { BinOpExpr AND v1 v2 }
  ;

p_Compare_Expression:
  | v1 = p_Not_Expression
    { v1 }
  | v1 = p_Compare_Expression; LES; v2 = p_Not_Expression
    { BinOpExpr LT v1 v2 }
  | v1 = p_Compare_Expression; GRE; v2 = p_Not_Expression
    { BinOpExpr GT v1 v2 }
  | v1 = p_Compare_Expression; GREEQ; v2 = p_Not_Expression
    { BinOpExpr GE v1 v2 }
  | v1 = p_Compare_Expression; LESEQ; v2 = p_Not_Expression
    { BinOpExpr LE v1 v2 }
  | v1 = p_Compare_Expression; NE; v2 = p_Not_Expression
    { BinOpExpr NE v1 v2 }
  | v1 = p_Compare_Expression; EQ; v2 = p_Not_Expression
    { BinOpExpr EQ v1 v2 }
  ;

p_Not_Expression:
  | v1 = p_Additive_Expression
    { v1 }
  | NOT v1 = p_Not_Expression
    { UnOpExpr NOT v1 }
  ;

p_Additive_Expression:
  | v1 = p_Multiplicative_Expression
    { v1 }
  | v1 = p_Additive_Expression; ADD; v2 = p_Multiplicative_Expression
    { BinOpExpr ADD v1 v2 }
  | v1 = p_Additive_Expression; MINUS; v2 = p_Multiplicative_Expression
    { BinOpExpr SUB v1 v2 }
  ;

p_Multiplicative_Expression:
  | v1 = p_When_Expression
    { v1 }
  | v1 = p_Multiplicative_Expression; MUL; v2 = p_When_Expression
    { BinOpExpr MUL v1 v2 }
  | v1 = p_Multiplicative_Expression; DIVF; v2 = p_When_Expression
    { BinOpExpr DIVF v1 v2 }
  | v1 = p_Multiplicative_Expression; DIV; v2 = p_When_Expression
    { BinOpExpr DIV v1 v2 }
  | v1 = p_Multiplicative_Expression; MOD; v2 = p_When_Expression
    { BinOpExpr MOD v1 v2 }
  ;

p_When_Expression:
  | v1 = p_Unary_Expression
    { v1 }
	| v1 = p_When_Expression; WHEN; v2 = IDENT
		{ WhenExpr v1 true {| name := v2; key := intern_string v2 |} }
	|	v1 = p_When_Expression; WHEN; NOT; v2 = IDENT
		{ WhenExpr v1 false {| name := v2; key := intern_string v2 |} }
  | v1 = p_When_Expression; WHEN; NOT; LPAREN; v2 = IDENT; RPAREN
    { WhenExpr v1 false {| name := v2; key := intern_string v2 |} }
  ;

p_Unary_Expression:
  | v1 = p_Nary_Expression
    { v1 }
//  | CURRENT; v1 = p_Unary_Expression
//    { CurrentExpr v1 }
  | ADD; v1 = p_Unary_Expression
    { UnOpExpr POS v1 }
  | MINUS; v1 = p_Unary_Expression
    { UnOpExpr NEG v1 }
  | v1 = p_Atom_Type; v2 = p_Unary_Expression
    { UnOpExpr (AtomTypeOp v1) v2 }
  ;

p_Nary_Expression:
  | v1 = p_Access_Expression
    { v1 }
  | DIESE; v1 = p_Nary_Expression
    { DieseExpr v1 }
  | NOR; v1 = p_Nary_Expression
    { NorExpr v1 }
  | PRE; v1 = p_Nary_Expression
    { PreExpr v1 }
  | CURRENT; v1 = p_Nary_Expression
    { CurrentExpr v1 }
  ;

p_Access_Expression:
  | v1 = p_Primary_Expression
    { v1 }
  | v1 = p_Access_Expression; DOT; v2 = IDENT
    { FieldExpr v1 {| name := v2; key := intern_string v2 |} }
  | v1 = p_Access_Expression; LBRACKET; v2 = p_Const_Expression; RBRACKET
    { ArrAccessExpr v1 v2 }
  | LPAREN; v1 = p_Access_Expression; DOT; v2 = p_Projection_Index_List; DEFAULT; v3 = p_Expression; RPAREN
    { DynamicProjectExpr v1 (cons_exprlist v2) v3 }
  ;

p_Projection_Index_List:
  | v1 = p_Projection_Index; v2 = p_Projection_Index_List
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

p_Projection_Index:
  | LBRACKET; v1 = p_Expression; v2 = RBRACKET
    { v1 }
  ;

p_Primary_Expression:
  | v1 = p_Atom_Expression
    { AtomExpr v1 }
  | LPAREN; v1 = p_Expression_List; RPAREN
    { ExprList (cons_exprlist v1) }
  | v1 = p_Case_Expression
    { v1 }
  | v1 = p_Struct_Construct_Expression
    { v1 }
  | v1 = p_Array_Construct_Expression
    { v1 }
  | v1 = p_With_Construct_Expression
    { v1 }
  | v1 = p_Prefix_Expression
    { v1 }
  | v1 = p_High_Order_Expression
    { v1 }
  | v1 = p_Tempo_Expression
    { v1 }
  | v1 = p_Merge_Expression
    { v1 }
  ;

p_Expression_List:
  | v1 = p_Nonempty_Expression_List
    { v1 }
  | (* empty *)
    { [] }
  ;
 
p_Nonempty_Expression_List:
  | v1 = p_Expression; COMMA; v2 = p_Nonempty_Expression_List
    { v1 :: v2 }
  | v1 = p_Expression
    { [v1] }
  ;

p_Case_Expression:
  | LPAREN; CASE; v1 = p_Expression; OF; v2 = p_Pattern_Expression_List; RPAREN
    { CaseExpr v1 (cons_caselist v2) }
  ;

p_Pattern_Expression_List:
  | v1 = p_Pattern_Expression; v2 = p_Pattern_Expression_List
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

p_Pattern_Expression:
  | SEG; v1 = p_Pattern; COLON; v2 = p_Expression
    { (v1, v2) }
  ;

p_Pattern:
  | v1 = IDENT
    { PIdent {| name := v1; key := intern_string v1 |} }
  | v1 = CONST_CHAR
    { PChar {| name := v1; key := xH |} }
  | v1 = TRUE
    { PBool {| name := v1; key := xH |} }
  | v1 = FALSE
    { PBool {| name := v1; key := xH |} }
  | v1 = p_Const_Integer
    { PInt {| name := v1; key := xH |} }
  |	DEFAULTPATTERN
    { DefaultPattern }
  ;

p_Struct_Construct_Expression:
  | LBRACE; v1 = p_Struct_Field_List; RBRACE
    { NameConstructExpr (cons_namelist v1) }
  ;

p_Struct_Field_List:
  | v1 = p_Struct_Field; COMMA; v2 = p_Struct_Field_List
    { v1 :: v2 }
  | v1 = p_Struct_Field
    { [v1] }
  ;

p_Struct_Field:
  | v1 = IDENT; COLON; v2 = p_Expression
    { ({| name := v1; key := intern_string v1 |}, v2) }
  ;

p_Array_Construct_Expression:
  | v1 = p_Primary_Expression; CARET; v2 = p_Const_Primary_Expression
    { ArrInitExpr v1 v2 }
  | LBRACKET; v1 = p_Expression_List; RBRACKET
    { ArrConstructExpr (cons_exprlist v1) }
  ;

p_With_Construct_Expression:
  | LPAREN; v1 = IDENT; WITH; v2 = p_Label_Index_List; EQ; v3 = p_Expression; RPAREN
    { NameWithExpr {| name := v1; key := intern_string v1 |} (cons_withlist v2) v3 }
  ;

p_Label_Index_List:
  | v1 = p_Label_Index; v2 = p_Label_Index_List
    { v1 :: v2 }
  | (* empty *)
    { [] }
  ;

p_Label_Index:
  | DOT; v1 = IDENT
    { FieldItem {| name := v1; key := intern_string v1 |} }
  | LBRACKET; v1 = p_Expression; RBRACKET
    { AccessItem v1 }
  ;

p_Prefix_Expression:
  | v1 = p_Prefix_Operator; LPAREN; v2 = p_Expression_List; RPAREN
    { PrefixExpr v1 (cons_exprlist v2) }
  ;

p_Prefix_Operator:
  | v1 = IDENT
    { Ident {| name := v1; key := intern_string v1 |} }
  | v1 = p_Prefix_Unary_Operator
    { UnOp v1 }
  | v1 = p_Prefix_Binary_Operator
    { BinOp v1 }
  ;

p_Prefix_Unary_Operator:
	|	SHORTSSS	
    { PSHORT }
	|	INTSSS		
    { PINT }
	|	FLOATSSS	
    { PFLOAT }
	|	REALSSS		
    { PREAL }
	|	NOTSSS		
    { PNOT }
	|	ADDSSS		
    { PPOS }
	|	MINUSSSS	
    { PNEG }
  ;

p_Prefix_Binary_Operator:
	| SSSADDSSS	
    { ADD }
	|	SSSMINUSSSS	
    { SUB }
	|	SSSMULSSS	
    { MUL }
	|	SSSDIVFSSS	
    { DIVF }
	|	SSSDIVSSS	
    { DIV }
	|	SSSMODSSS	
    { MOD }
	|	SSSANDSSS	
    { AND }
	|	SSSORSSS	
    { OR }
	|	SSSXORSSS	
    { XOR }
	|	SSSGRESSS	
    { GT }
	|	SSSGREEQSSS	
    { GE }
	|	SSSLESSSS	
    { LT }
	|	SSSLESEQSSS	
    { LE }
	|	SSSEQSSS	
    { EQ }
	|	SSSNESSS	
    { NE }
  ;

p_High_Order_Expression:
  | v1 = p_High_Order_Operator; 
    LES; LES; v2 = p_Prefix_Operator; SEMICOLON; v3 = p_Const_Primary_Expression; GRE; GRE; 
    LPAREN; v4 = p_Expression_List; RPAREN
    { HighOrderExpr v1 v2 v3 (cons_exprlist v4) }
  | v1 = p_High_Order_Operator; 
    LES; LES; v2 = p_Prefix_Operator; COMMA; v3 = p_Const_Primary_Expression; GRE; GRE; 
    LPAREN; v4 = p_Expression_List; RPAREN
    { HighOrderExpr v1 v2 v3 (cons_exprlist v4) }
  ;

p_High_Order_Operator:
  | MAP	
    { MAP }
  | RED	
    { RED }
  | FILL	
    { FILL }
  | FILLRED	
    { FILLRED }
  ;

p_Tempo_Expression:
  | BOOLRED; LES; LES; v1 = p_Const_Integer; COMMA; v2 = p_Const_Integer; GRE; GRE; LPAREN; v3 = p_Expression; RPAREN
    { BoolredExpr v1 v2 v3 }
  | FBY; LPAREN; v1 = p_Expression_List; SEMICOLON; v2 = p_Const_Expression; SEMICOLON; v3 = p_Expression_List; RPAREN
    { FbyExpr (cons_exprlist v1) v2 (cons_exprlist v3) }
  | LPAREN; v1 = p_Nonempty_Expression_List; FBY; v2 = p_Nonempty_Expression_List; RPAREN
    { FbyExpr (cons_exprlist v2) (CEAtom ( EInt {| name := ocaml_string "1"; key := xH |} )) (cons_exprlist v1) }
  ;
  ;

p_Merge_Expression:
  | MERGE; v1 = IDENT; v2 = p_Atom_Expression; LPAREN; v3 = p_Expression; RPAREN
    { MergeExpr {| name := v1; key := intern_string v1 |} (AtomExpr v2) v3 }
  | MERGE; v1 = IDENT; LPAREN; v2 = p_Expression; RPAREN; v3 = p_Atom_Expression
    { MergeExpr {| name := v1; key := intern_string v1 |} v2 (AtomExpr v3) }
  | MERGE; v1 = IDENT; v2 = p_Atom_Expression; v3 = p_Atom_Expression
    { MergeExpr {| name := v1; key := intern_string v1 |} (AtomExpr v2) (AtomExpr v3) }
  | MERGE; v1 = IDENT; LPAREN; v2 = p_Expression; RPAREN; LPAREN; v3 = p_Expression; RPAREN
    { MergeExpr {| name := v1; key := intern_string v1 |} v2 v3 }
  ;

p_Const_Integer:
  | const_int = CONST_INT	
    { const_int }
	|	ADD; const_int = CONST_INT
    { const_int }
	|	MINUS; const_int = CONST_INT 
    { String.append "-" const_int }
  ;
