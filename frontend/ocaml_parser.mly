/* File ocaml_parser.mly */

/* header */
%{
	let parse_error s =
		print_string s;
	;;

    open Tree
	open BinNums
	open Camlcoq

	let rec cons_fieldlist l =
          match l with
          | [] -> Fnil
          | (id,ty) :: tl -> Fcons (id, ty, cons_fieldlist tl) 

        let rec cons_constexprlist l =
          match l with
          | [] -> CEnil
          | e :: tl -> CEcons (e, cons_constexprlist tl) 

        let rec cons_conststructlist l =
          match l with
          | [] -> CNamesNil
          | (id, e) :: tl -> CNamesCons (id, e, cons_conststructlist tl) 

        let rec cons_exprlist l =
          match l with
          | [] -> Enil
          | e :: tl -> Econs (e, cons_exprlist tl) 

        let rec cons_namelist l =
          match l with
          | [] -> NamesNil
          | (id, e) :: tl -> NamesCons (id, e, cons_namelist tl) 

        let rec cons_caselist l =
          match l with
          | [] -> CasesNil
          | (p, e) :: tl -> CasesCons (p, e, cons_caselist tl) 

        let rec cons_withlist l =
          match l with
          | [] -> WithNil
          | it :: tl -> WithCons (it, cons_withlist tl) 

   
	(*let first_unused_ident () = !next_atom*)

%}

/* ? for xu: I can't compile lexer.mll. Please use make to have a try. */
/* ? for xu: There is no filed. It's field. */

/* ? for zhu: check integer and Int */

/* tokens */
/* keywords */
%token TYPE FUNCTION NODE RETURNS LET TEL
%token VAR CONST PRE FBY IF THEN ELSE WHEN CURRENT MERGE CASE OF DEFAULTPATTERN ARROW SEG ENUM MAKE FLATTEN WITH
%token SHORTSSS INTSSS FLOATSSS REALSSS NOTSSS ADDSSS MINUSSSS
%token SSSADDSSS SSSMINUSSSS SSSMULSSS SSSDIVFSSS SSSDIVSSS SSSMODSSS SSSANDSSS SSSORSSS SSSXORSSS
%token SSSEQSSS SSSNESSS SSSGRESSS SSSGREEQSSS SSSLESSSS SSSLESEQSSS
%token MAP RED FILL FILLRED BOOLRED DIESE NOR DEFAULT
%token CHAR BOOL SHORT USHORT INT UINT FLOAT REAL

%token NOT ADD MINUS MUL DIVF DIV MOD AND OR XOR LESEQ GREEQ NE EQ LES GRE

%left IF THEN ELSE ARROW
%left OR XOR
%left AND
%right NOT
%left LES LESEQ EQ GREEQ GRE NE
%left ADD MINUS
%left MUL DIVF DIV MOD
%left CARET
%nonassoc UNOPEXP PREEXP

%token TRUE FALSE
%token <string> CONST_USINT CONST_SINT CONST_UINT CONST_INT CONST_FLO CONST_REAL IDENT CONST_CHAR

%token LPAREN RPAREN COMMA COLON SEMICOLON CARET LBRACKET RBRACKET LBRACE RBRACE DOT

%token EOF


%start programY			/* the entry point */
%type <Tree.program> programY
%%

programY: nodeBlksY EOF
	{$1}
;

nodeBlksY:
		nodeBlkY nodeBlksY	{$1::$2}
	|						{[]}

nodeBlkY:
		typeBlkY	{$1}
	|	constBlkY	{$1}
	|	funcBlkY	{$1}
;

typeBlkY:
	TYPE typeStmtsY	{TypeBlk $2}
;

typeStmtsY:
		typeStmtY typeStmtsY	{$1::$2}
	|						{[]}
;

typeStmtY:
	IDENT EQ kindY SEMICOLON
		{TypeStmt({ name = $1; key = intern_string $1 }, $3)}
;

kindY:
		atomTypeY			{AtomType $1}
	|	structTypeY			{$1}
	|	kindY CARET constExprY	{Array($1, $3)}
	|	enumTypeY			{$1}
	| 	IDENT 				{TypeDef {name = $1; key = intern_string $1}}
;

enumTypeY:
	ENUM LBRACE identsY RBRACE
		{EnumType $3}
;

structTypeY:
	LBRACE fieldsY RBRACE
		{Struct (cons_fieldlist $2)}
;

fieldsY:
		fieldY COMMA fieldsY	{List.append $1 $3}
	|	fieldY					{$1}
;

fieldY:
	identsY COLON kindY
		{List.map (fun i -> (i, $3)) $1}
;

atomTypeY:
		CHAR	{Char}
	|	BOOL	{Bool}
	|	INT		{Int}
	|	UINT	{UInt}
	|	SHORT	{Short}
	|	USHORT	{UShort}
	|	FLOAT	{Float}
	|	REAL	{Real}
;

constBlkY:
	CONST constStmtsY
		{ConstBlk $2}
;

constStmtsY:
		constStmtY constStmtsY	{$1::$2}
	|							{[]}
;

constStmtY:
	IDENT COLON kindY EQ constExprY SEMICOLON
		{ConstStmt({ name = $1; key = intern_string $1 }, $3, $5)}
;

funcBlkY:
	funcTypeY IDENT paramBlkY returnBlkY funcBodyY
		{FuncBlk($1, { name = $2; key = intern_string $2 }, $3, $4, $5)}
;

funcTypeY:
		FUNCTION	{Function}
	|	NODE		{Node}
;

paramBlkY:
	LPAREN params2Y RPAREN
		{($2)}
;

returnBlkY:
	    RETURNS LPAREN params2Y RPAREN
	        {($3)}
	|   RETURNS LPAREN params2Y RPAREN SEMICOLON
	        {($3)}
;

paramY:
		identsY COLON kindY
			{List.map (fun i -> ((i, $3), NOCLOCK)) $1}
	|	identsY COLON kindY WHEN IDENT
			{List.map (fun i -> ((i, $3), Clock (true, { name = $5; key = intern_string $5 }))) $1}
	| 	identsY COLON kindY WHEN NOT IDENT
			{List.map (fun i -> ((i, $3), Clock (false, { name = $6; key = intern_string $6 }))) $1}
;




params2Y:
		paramY SEMICOLON params2Y	{List.append $1 $3}
	|	paramY						{$1}
	|								{[]}
;

funcBodyY:
		varBlkY LET eqStmtsY TEL	{BodyBlk($1, $3)}
	|	varBlkY LET eqStmtsY TEL SEMICOLON	{BodyBlk($1, $3)}
;

varBlkY:
		VAR vars3Y	{VarList $2}
	|				{NOVARBLK}
;

vars3Y:
		paramY SEMICOLON vars3Y	{List.append $1 $3}
	|								{[]}
;

eqStmtsY:
		eqStmtY eqStmtsY	{$1::$2}
	|					{[]}
;

eqStmtY:
		lhsLY EQ simplFbyExprY SEMICOLON
		{EqStmt($1, $3)}
	|	lhsLY EQ exprY SEMICOLON
		{EqStmt($1, $3)}
;

lhsLY:
		lhs COMMA lhsLY	{$1::$3}
	|	lhs				{[$1]}
	|   LPAREN lhsLY RPAREN {$2}
;

lhs:
		IDENT			{{ name = $1; key = intern_string $1 }}
;

identsY:
		IDENT COMMA identsY	{{ name = $1; key = intern_string $1} :: $3}
	|	IDENT				{[{ name = $1; key = intern_string $1 }]}
;

atomExprY:
		IDENT		{EIdent { name = $1; key = intern_string $1 }}
	|	new_USINT	{EUShort { name = $1; key = Coq_xH }}
	|	new_SINT	{EShort { name = $1; key = Coq_xH }}
	|	new_INT		{EInt { name = $1; key = Coq_xH }}
	|	new_UINT	{EUInt { name = $1; key = Coq_xH }}
	|	new_REAL	{EReal { name = $1; key = Coq_xH }}
	|	new_FLO		{EFloat { name = $1; key = Coq_xH }}
	|	CONST_CHAR	{EChar { name = $1; key = Coq_xH }}
	|	TRUE		{EBool { name = "true"; key = Coq_xH }}
	|	FALSE		{EBool { name = "false"; key = Coq_xH}}
;

constFieldY:
	identsY COLON constExprY
		{List.map (fun i -> (i, $3)) $1}
;

constFieldsY:
		constFieldY COMMA constFieldsY	{List.append $1 $3}
	| 	constFieldY    	  		{$1}
;

constBinOpExprY:
		constExprY OR constExprY
			{CEBinOpExpr(OR, $1, $3)}
	|	constExprY XOR constExprY
			{CEBinOpExpr(XOR, $1, $3)}
	|	constExprY AND constExprY
			{CEBinOpExpr(AND, $1, $3)}
	|	constExprY LES constExprY
			{CEBinOpExpr(LT, $1, $3)}
	|	constExprY GRE constExprY
			{CEBinOpExpr(GT, $1, $3)}
	|	constExprY GREEQ constExprY
			{CEBinOpExpr(GE, $1, $3)}
	|	constExprY LESEQ constExprY
			{CEBinOpExpr(LE, $1, $3)}
	|	constExprY NE constExprY
			{CEBinOpExpr(NE, $1, $3)}
	|	constExprY EQ constExprY
			{CEBinOpExpr(EQ, $1, $3)}
	|	constExprY ADD constExprY
			{CEBinOpExpr(ADD, $1, $3)}
	|	constExprY MINUS constExprY
			{CEBinOpExpr(SUB, $1, $3)}
	|	constExprY MUL constExprY
			{CEBinOpExpr(MUL, $1, $3)}
	|	constExprY DIVF constExprY
			{CEBinOpExpr(DIVF, $1, $3)}
	|	constExprY DIV constExprY
			{CEBinOpExpr(DIV, $1, $3)}
	|	constExprY MOD constExprY
			{CEBinOpExpr(MOD, $1, $3)}
;

constUnOpExprY:
	unOpY constExprY
		{CEUnOpExpr($1, $2)}
;

constExprY:
		atomExprY	    		{CEAtom $1}
        |       constUnOpExprY      		{$1}
        |	constBinOpExprY	    		{$1}
	|	LPAREN constExprY RPAREN	{$2} 
	| 	LBRACKET constExprsY RBRACKET 	{CEArray (cons_constexprlist $2)}
	| 	LBRACE constFieldsY RBRACE	{CEConstructor (cons_conststructlist $2)}
;

constExprsY:
		constExprY COMMA constExprsY	{$1 :: $3}
	|	constExprY      		{[$1]}
;


unOpY:
		atomTypeY	{AtomTypeOp $1}
	|	NOT			{NOT}
	|	ADD			{POS}
	|	MINUS		{NEG}
;

binOpExprY:
		exprY OR exprY
			{BinOpExpr(OR, $1, $3)}
	|	exprY XOR exprY
			{BinOpExpr(XOR, $1, $3)}
	|	exprY AND exprY
			{BinOpExpr(AND, $1, $3)}
	|	exprY LES exprY
			{BinOpExpr(LT, $1, $3)}
	|	exprY GRE exprY
			{BinOpExpr(GT, $1, $3)}
	|	exprY GREEQ exprY
			{BinOpExpr(GE, $1, $3)}
	|	exprY LESEQ exprY
			{BinOpExpr(LE, $1, $3)}
	|	exprY NE exprY
			{BinOpExpr(NE, $1, $3)}
	|	exprY EQ exprY
			{BinOpExpr(EQ, $1, $3)}
	|	exprY ADD exprY
			{BinOpExpr(ADD, $1, $3)}
	|	exprY MINUS exprY
			{BinOpExpr(SUB, $1, $3)}
	|	exprY MUL exprY
			{BinOpExpr(MUL, $1, $3)}
	|	exprY DIVF exprY
			{BinOpExpr(DIVF, $1, $3)}
	|	exprY DIV exprY
			{BinOpExpr(DIV, $1, $3)}
	|	exprY MOD exprY
			{BinOpExpr(MOD, $1, $3)}
;

fieldExprY:
	exprY DOT IDENT
		{FieldExpr($1, { name = $3; key = intern_string $3 })}
;

exprsY:
		exprY COMMA exprsY	{$1::$3}
	|	exprY				{[$1]}
	|						{[]}
;

dynamicProjectExprY:
	LPAREN exprY DOT bracketExprsY DEFAULT exprY RPAREN
		{DynamicProjectExpr($2, cons_exprlist $4, $6)}
;

bracketExprsY:
		bracketExprY bracketExprsY	{$1::$2}
	|								{[]}
;

bracketExprY:
	LBRACKET exprY RBRACKET
		{$2}
;

arrAccessExprY:
	exprY LBRACKET constExprY RBRACKET
		{ArrAccessExpr($1, $3)}
;

arrInitExprY:
	exprY CARET constExprY
		{ArrInitExpr($1, $3)}
;

arrConstructExprY:
	LBRACKET exprsY RBRACKET
		{ArrConstructExpr (cons_exprlist $2)}
;

arrNameConstructExprY:
	LBRACE nameArrItemsY RBRACE
		{NameConstructExpr (cons_namelist $2)}
;

nameArrItemsY:
		nameArrItemY COMMA nameArrItemsY	{$1::$3}
	|	nameArrItemY						{[$1]}
;

nameArrItemY:
	IDENT COLON exprY
		{({ name = $1; key = intern_string $1 }, $3)}
;

fbyExprY:
		FBY LPAREN exprsY SEMICOLON constExprY SEMICOLON exprsY RPAREN
		{FbyExpr(cons_exprlist $3, $5, cons_exprlist $7)}
	|	LPAREN exprsY FBY exprsY RPAREN
		{FbyExpr(cons_exprlist $4, (CEAtom (EInt {name = "1"; key = intern_string "1" })), cons_exprlist $2)}
;

simplFbyExprY:
	exprsY FBY exprsY
		{FbyExpr(cons_exprlist $3, (CEAtom (EInt {name = "1"; key = intern_string "1" })), cons_exprlist $1)}
;

whenExprY:
		exprY WHEN IDENT
			{WhenExpr($1, true, { name = $3; key = intern_string $3 })}
	|	exprY WHEN NOT IDENT
			{WhenExpr($1, false, { name = $4; key = intern_string $4 })}
;

mergeExprY:
		MERGE IDENT atomExprY LPAREN exprY RPAREN
			{MergeExpr({ name = $2; key = intern_string $2 }, (AtomExpr $3), $5)}
	|	MERGE IDENT LPAREN exprY RPAREN atomExprY
			{MergeExpr({ name = $2; key = intern_string $2 }, $4, (AtomExpr $6))}
	|	MERGE IDENT atomExprY atomExprY
			{MergeExpr({ name = $2; key = intern_string $2 }, (AtomExpr $3), (AtomExpr $4))}
	|	MERGE IDENT LPAREN exprY RPAREN LPAREN exprY RPAREN
			{MergeExpr({ name = $2; key = intern_string $2 }, $4, $7)}
;


ifExprY:
	IF exprY THEN exprY ELSE exprY
		{IfExpr($2, $4, $6)}
;

caseExprY:
	LPAREN CASE exprY OF casesY RPAREN
		{CaseExpr($3, cons_caselist $5)}
;

casesY:
		caseItemY casesY	{$1::$2}
	|						{[]}
;

caseItemY:
	SEG patternY COLON exprY
		{($2, $4)}
;

nameWithExprY:
	LPAREN IDENT WITH nameWithItemsY EQ exprY RPAREN
		{NameWithExpr({ name = $2; key = intern_string $2 }, cons_withlist $4, $6)}
;

nameWithItemsY:
		nameWithItemY nameWithItemsY	{$1::$2}
	|						{[]}
;

nameWithItemY:
		DOT IDENT				{FieldItem { name = $2; key = intern_string $2 }}
	|	LBRACKET exprY RBRACKET	{AccessItem $2}
;

patternY:
		IDENT				{PIdent { name = $1; key = intern_string $1 }}
	|	new_INT				{PInt { name = $1; key = Coq_xH }}
	|	CONST_CHAR			{PChar { name = $1; key = Coq_xH }}
	|	TRUE				{PBool { name = "true"; key = Coq_xH }}
	|	FALSE				{PBool { name = "false"; key = Coq_xH }}
	|	DEFAULTPATTERN		{DefaultPattern}
;

exprListY:
	exprsY
		{ExprList (cons_exprlist $1)}
;

prefixExprY:
	prefixOpY LPAREN exprsY RPAREN
		{PrefixExpr($1, cons_exprlist $3)}
;

prefixOpY:
		IDENT 			{Ident { name = $1; key = intern_string $1 }}
	|	prefixUnOpY		{UnOp $1}
	|	prefixBinOpY		{BinOp $1}
;

prefixUnOpY:
		SHORTSSS	{PSHORT}
	|	INTSSS		{PINT}
	|	FLOATSSS	{PFLOAT}
	|	REALSSS		{PREAL}
	|	NOTSSS		{PNOT}
	|	ADDSSS		{PPOS}
	|	MINUSSSS	{PNEG}
;

prefixBinOpY:
		SSSADDSSS	{ADD}
	|	SSSMINUSSSS	{SUB}
	|	SSSMULSSS	{MUL}
	|	SSSDIVFSSS	{DIVF}
	|	SSSDIVSSS	{DIV}
	|	SSSMODSSS	{MOD}
	|	SSSANDSSS	{AND}
	|	SSSORSSS	{OR}
	|	SSSXORSSS	{XOR}
	|	SSSGRESSS	{GT}
	|	SSSGREEQSSS	{GE}
	|	SSSLESSSS	{LT}
	|	SSSLESEQSSS	{LE}
	|	SSSEQSSS	{EQ}
	|	SSSNESSS	{NE}
;

highOrderExprY:
		highOrderOpY LES LES prefixOpY SEMICOLON constExprY GRE GRE LPAREN exprsY RPAREN
			{HighOrderExpr($1, $4, $6, cons_exprlist $10)}
	|  	highOrderOpY LES LES prefixOpY COMMA constExprY GRE GRE LPAREN exprsY RPAREN
       		{HighOrderExpr($1, $4, $6, cons_exprlist $10)}

;

highOrderOpY:
		MAP	{MAP}
	|	RED	{RED}
	|	FILL	{FILL}
	|	FILLRED	{FILLRED}
;

boolredExprY:
        BOOLRED LES LES new_INT COMMA new_INT GRE GRE LPAREN exprY RPAREN
            {BoolredExpr($4, $6, $10)}
;

dieseExprY:
        	DIESE exprY			{DieseExpr($2)}
	|	DIESE LPAREN exprsY RPAREN	{DieseExpr(ExprList(cons_exprlist $3))}
            
;

norExprY:
        	NOR exprY			{NorExpr($2)}
	|	NOR LPAREN exprsY RPAREN	{NorExpr(ExprList(cons_exprlist $3))}
;

exprY:
		atomExprY			{AtomExpr $1}
	|	unOpY exprY	%prec	UNOPEXP	{UnOpExpr($1, $2)}
	|	binOpExprY			{$1}
	|	fieldExprY			{$1}
	|	dynamicProjectExprY		{$1}
	|	arrAccessExprY			{$1}
	|	arrInitExprY			{$1}
	|	arrConstructExprY		{$1}
	|	arrNameConstructExprY		{$1}
	|	PRE exprY	%prec	PREEXP	{PreExpr $2}
	|	CURRENT exprY			{CurrentExpr $2}
	|	fbyExprY			{$1}
	|	exprY ARROW exprY		{ArrowExpr($1, $3)}
	|	whenExprY			{$1}
	|	mergeExprY			{$1}
	|	ifExprY				{$1}
	|	caseExprY			{$1}
	|	nameWithExprY			{$1}
	|	LPAREN exprListY RPAREN		{$2}
/*	|	LPAREN exprY RPAREN		{$2} */
	|	prefixExprY			{$1}
	|	highOrderExprY			{$1}
	|	boolredExprY			{$1}
	|	dieseExprY			{$1}
	|	norExprY			{$1}
;


new_INT:
		CONST_INT	{$1}
	|	ADD CONST_INT	{$2}
	|	MINUS CONST_INT {"-" ^ $2}
;

new_SINT:
		CONST_SINT	{$1}
	|	ADD CONST_SINT	{$2}
	|	MINUS CONST_SINT {"-" ^ $2}
;

new_USINT:
		CONST_USINT	{$1}
	|	ADD CONST_USINT	{$2}
	|	MINUS CONST_USINT {"-" ^ $2}
;

new_UINT:
		CONST_UINT	{$1}
	|	ADD CONST_UINT	{$2}
	|	MINUS CONST_UINT {"-" ^ $2}
;

new_REAL:
		CONST_REAL	{$1}
	|	ADD CONST_REAL	{$2}
	|	MINUS CONST_REAL {"-" ^ $2}
;

new_FLO:
		CONST_FLO	{$1}
	|	ADD CONST_FLO	{$2}
	|	MINUS CONST_FLO {"-" ^ $2}
;
