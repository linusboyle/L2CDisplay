(*
    Boilerplate necessary for converting between OCaml types and extracted Coq
    types without using Obj.magic.
*)

Require Import String.
Require Import Parser.

Definition str := string.

Inductive token_id :=
  (* One character token *)
  | COMMA'token
  | COLON'token
  | SEMICOLON'token
  | CARET'token
  (* Prefix unary operator token *)
  | SHORTSSS'token
	| INTSSS'token
	| FLOATSSS'token
	| REALSSS'token
	| NOTSSS'token
	| ADDSSS'token
	| MINUSSSS'token
  (* Prefix binary operator token *)
  | SSSADDSSS'token
	| SSSMINUSSSS'token
	| SSSMULSSS'token
	| SSSDIVFSSS'token
	| SSSDIVSSS'token
	| SSSMODSSS'token
	| SSSANDSSS'token
	| SSSORSSS'token
	| SSSXORSSS'token
	| SSSEQSSS'token
	| SSSNESSS'token
	| SSSGRESSS'token
	| SSSGREEQSSS'token
	| SSSLESSSS'token
	| SSSLESEQSSS'token
  (* Operator token *)
  | ADD'token
  | MINUS'token
  | MUL'token
  | DIVF'token
  | EQ'token
  | NE'token
  | LES'token
  | GRE'token
  | LESEQ'token
  | GREEQ'token
  | ARROW'token
  | DIESE'token
  | SEG'token
  | DOT'token
  | DEFAULTPATTERN'token
  | NOR'token
  | NOT'token
  | DIV'token
  | MOD'token
  | AND'token
  | OR'token
  | XOR'token
  | LPAREN'token
  | RPAREN'token
  | LBRACE'token
  | RBRACE'token
  | LBRACKET'token
  | RBRACKET'token
  (* Type keyword token *)
  | TYPE'token
  | CONST'token
  | FUNCTION'token
  | NODE'token
  | ENUM'token
  | BOOL'token
  | USHORT'token
  | SHORT'token
  | UINT'token
  | INT'token
  | REAL'token
  | FLOAT'token
  | CHAR'token
  | TRUE'token : str -> token_id
  | FALSE'token : str -> token_id
  (* Keyword Token *)
  | VAR'token
  | LET'token
  | TEL'token
  | RETURNS'token
  | PRE'token
  | FBY'token
  | IF'token
  | THEN'token
  | ELSE'token
  | WHEN'token
  | CASE'token
  | OF'token
  | DEFAULT'token
  | WITH'token
  | BOOLRED'token
  | MAP'token
  | RED'token
  | FILL'token
  | FILLRED'token
  | MERGE'token
  | CURRENT'token
  (* Type token *)
  | IDENT'token : str -> token_id
  | CONST_CHAR'token : str -> token_id
  | CONST_INT'token : str -> token_id
  | CONST_UINT'token : str -> token_id
  | CONST_SHORT'token : str -> token_id
  | CONST_USHORT'token : str -> token_id
  | CONST_FLOAT'token : str -> token_id
  | CONST_REAL'token : str -> token_id
  (* End-of-file token *)
  | EOF'token
  .

(*
    Helper function to make expressions in get_token more readable.
    Essentially, get_type just takes a terminal and a value of its
    corresponding semantic type, returning a token. This should likely be
    generated by "menhir --coq", but isn't yet.
*)
Definition get_type (t : Gram.terminal) (sst : Gram.symbol_semantic_type (Gram.T t)) : Gram.token :=
  existT (fun t' => Gram.symbol_semantic_type (Gram.T t')) t sst.

Definition get_token (t : token_id) : Aut.GramDefs.token :=
  match t with
    (* One character token *)
    | COMMA'token =>
      get_type Gram.COMMA't tt
    | COLON'token =>
      get_type Gram.COLON't tt
    | SEMICOLON'token =>
      get_type Gram.SEMICOLON't tt
    | CARET'token =>
      get_type Gram.CARET't tt
    (* Prefix unary operator token *)
    | SHORTSSS'token =>
      get_type Gram.SHORTSSS't tt
    | INTSSS'token =>
      get_type Gram.INTSSS't tt
    | FLOATSSS'token =>
      get_type Gram.FLOATSSS't tt
    | REALSSS'token =>
      get_type Gram.REALSSS't tt
    | NOTSSS'token =>
      get_type Gram.NOTSSS't tt
    | ADDSSS'token =>
      get_type Gram.ADDSSS't tt
    | MINUSSSS'token =>
      get_type Gram.MINUSSSS't tt
    (* Prefix binary operator token *)
    | SSSADDSSS'token =>
      get_type Gram.SSSADDSSS't tt
    | SSSMINUSSSS'token =>
      get_type Gram.SSSMINUSSSS't tt
    | SSSMULSSS'token =>
      get_type Gram.SSSMULSSS't tt
    | SSSDIVFSSS'token =>
      get_type Gram.SSSDIVFSSS't tt
    | SSSDIVSSS'token =>
      get_type Gram.SSSDIVSSS't tt
    | SSSMODSSS'token =>
      get_type Gram.SSSMODSSS't tt
    | SSSANDSSS'token =>
      get_type Gram.SSSANDSSS't tt
    | SSSORSSS'token =>
      get_type Gram.SSSORSSS't tt
    | SSSXORSSS'token =>
      get_type Gram.SSSXORSSS't tt
    | SSSEQSSS'token =>
      get_type Gram.SSSEQSSS't tt
    | SSSNESSS'token =>
      get_type Gram.SSSNESSS't tt
    | SSSGRESSS'token =>
      get_type Gram.SSSGRESSS't tt
    | SSSGREEQSSS'token =>
      get_type Gram.SSSGREEQSSS't tt
    | SSSLESSSS'token =>
      get_type Gram.SSSLESSSS't tt
    | SSSLESEQSSS'token =>
      get_type Gram.SSSLESEQSSS't tt
    (* Operator Token *)
    | ADD'token =>
      get_type Gram.ADD't tt
    | MINUS'token =>
      get_type Gram.MINUS't tt
    | MUL'token =>
      get_type Gram.MUL't tt
    | DIVF'token =>
      get_type Gram.DIVF't tt
    | EQ'token =>
      get_type Gram.EQ't tt
    | NE'token =>
      get_type Gram.NE't tt
    | LES'token =>
      get_type Gram.LES't tt
    | GRE'token =>
      get_type Gram.GRE't tt
    | LESEQ'token =>
      get_type Gram.LESEQ't tt
    | GREEQ'token =>
      get_type Gram.GREEQ't tt
    | ARROW'token =>
      get_type Gram.ARROW't tt
    | DIESE'token =>
      get_type Gram.DIESE't tt
    | SEG'token =>
      get_type Gram.SEG't tt
    | DOT'token =>
      get_type Gram.DOT't tt
    | DEFAULTPATTERN'token =>
      get_type Gram.DEFAULTPATTERN't tt
    | NOR'token =>
      get_type Gram.NOR't tt
    | NOT'token =>
      get_type Gram.NOT't tt
    | DIV'token =>
      get_type Gram.DIV't tt
    | MOD'token =>
      get_type Gram.MOD't tt
    | AND'token =>
      get_type Gram.AND't tt
    | OR'token =>
      get_type Gram.OR't tt
    | XOR'token =>
      get_type Gram.XOR't tt
    | LPAREN'token =>
      get_type Gram.LPAREN't tt
    | RPAREN'token =>
      get_type Gram.RPAREN't tt
    | LBRACE'token =>
      get_type Gram.LBRACE't tt
    | RBRACE'token =>
      get_type Gram.RBRACE't tt
    | LBRACKET'token =>
      get_type Gram.LBRACKET't tt
    | RBRACKET'token =>
      get_type Gram.RBRACKET't tt
    (* Type keyword token *)
    | TYPE'token =>
      get_type Gram.TYPE't tt
    | CONST'token =>
      get_type Gram.CONST't tt
    | FUNCTION'token =>
      get_type Gram.FUNCTION't tt
    | NODE'token =>
      get_type Gram.NODE't tt
    | ENUM'token =>
      get_type Gram.ENUM't tt
    | BOOL'token =>
      get_type Gram.BOOL't tt
    | USHORT'token =>
      get_type Gram.USHORT't tt
    | SHORT'token =>
      get_type Gram.SHORT't tt
    | UINT'token =>
      get_type Gram.UINT't tt
    | INT'token =>
      get_type Gram.INT't tt
    | REAL'token =>
      get_type Gram.REAL't tt
    | FLOAT'token =>
      get_type Gram.FLOAT't tt
    | CHAR'token =>
      get_type Gram.CHAR't tt
    | TRUE'token str =>
      get_type Gram.TRUE't str
    | FALSE'token str =>
      get_type Gram.FALSE't str
    (* Keyword Token *)
    | VAR'token =>
      get_type Gram.VAR't tt
    | LET'token =>
      get_type Gram.LET't tt
    | TEL'token =>
      get_type Gram.TEL't tt
    | RETURNS'token =>
      get_type Gram.RETURNS't tt
    | PRE'token =>
      get_type Gram.PRE't tt
    | FBY'token =>
      get_type Gram.FBY't tt
    | IF'token =>
      get_type Gram.IF't tt
    | THEN'token =>
      get_type Gram.THEN't tt
    | ELSE'token =>
      get_type Gram.ELSE't tt
    | WHEN'token =>
      get_type Gram.WHEN't tt
    | CASE'token =>
      get_type Gram.CASE't tt
    | OF'token =>
      get_type Gram.OF't tt
    | DEFAULT'token =>
      get_type Gram.DEFAULT't tt
    | WITH'token =>
      get_type Gram.WITH't tt
    | BOOLRED'token =>
      get_type Gram.BOOLRED't tt
    | MAP'token =>
      get_type Gram.MAP't tt
    | RED'token =>
      get_type Gram.RED't tt
    | FILL'token =>
      get_type Gram.FILL't tt
    | FILLRED'token =>
      get_type Gram.FILLRED't tt
    | MERGE'token =>
      get_type Gram.MERGE't tt
    | CURRENT'token =>
      get_type Gram.CURRENT't tt
    (* Type token *)
    | IDENT'token str =>
      get_type Gram.IDENT't str
    | CONST_CHAR'token const_char =>
      get_type Gram.CONST_CHAR't const_char
    | CONST_INT'token const_int =>
      get_type Gram.CONST_INT't const_int
    | CONST_UINT'token const_uint =>
      get_type Gram.CONST_UINT't const_uint
    | CONST_SHORT'token const_short =>
      get_type Gram.CONST_SHORT't const_short
    | CONST_USHORT'token const_ushort =>
      get_type Gram.CONST_USHORT't const_ushort
    | CONST_FLOAT'token const_float =>
      get_type Gram.CONST_FLOAT't const_float
    | CONST_REAL'token const_real =>
      get_type Gram.CONST_REAL't const_real
    (* End-of-file token *)
    | EOF'token =>
      get_type Gram.EOF't tt
  end.
