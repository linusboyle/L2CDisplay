%{
	let parse_error s =
		print_string s;
	;;

    open LDisplay
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
%}

%token TYPE FUNCTION NODE RETURNS LET TEL
%token VAR CONST PRE FBY IF THEN ELSE WHEN CURRENT MERGE CASE OF DEFAULTPATTERN ARROW SEG ENUM MAKE FLATTEN WITH
%token SHORTSSS INTSSS FLOATSSS REALSSS NOTSSS ADDSSS MINUSSSS
%token SSSADDSSS SSSMINUSSSS SSSMULSSS SSSDIVFSSS SSSDIVSSS SSSMODSSS SSSANDSSS SSSORSSS SSSXORSSS
%token SSSEQSSS SSSNESSS SSSGRESSS SSSGREEQSSS SSSLESSSS SSSLESEQSSS
%token MAP RED FILL FILLRED BOOLRED DIESE NOR DEFAULT
%token CHAR BOOL SHORT USHORT INT UINT FLOAT REAL
%token WIDGET CTRL
%token<string> MEGA

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
%type <LDisplay.program> programY
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
    |   widgetBlkY  {$1}
    |   ctrlBlkY    {$1}
;

typeBlkY:
	TYPE typeStmtsY	{TypeBlk $2}
;

typeStmtsY:
		typeStmtY typeStmtsY	{$1::$2}
	|						    {[]}
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
	|	BOOL	{Bool}
	|	INT		{Int}
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

widgetBlkY:
    WIDGET IDENT paramBlkY returnBlkY
        {WidgetBlk({ name = $2; key = intern_string $2}, $3, $4)}
;

ctrlBlkY:
    CTRL IDENT LPAREN RPAREN RETURNS LPAREN RPAREN funcBodyY
        {ControlBlk({name = $2; key = intern_string $2}, $8)}

funcTypeY:
		FUNCTION	{Function}
	|	NODE		{Node}
;

paramBlkY:
	LPAREN paramsY RPAREN
		{($2)}
;

returnBlkY:
	    RETURNS LPAREN paramsY RPAREN
	        {($3)}
	|   RETURNS LPAREN paramsY RPAREN SEMICOLON
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

paramsY:
		paramY SEMICOLON paramsY	{List.append $1 $3}
	|	paramY						{$1}
	|								{[]}
;

funcBodyY:
		varBlkY LET eqStmtsY TEL	{BodyBlk($1, $3)}
	|	varBlkY LET eqStmtsY TEL SEMICOLON	{BodyBlk($1, $3)}
;

varBlkY:
		VAR varsY	{$2}
    |				{[]}
;

varsY:
		paramY SEMICOLON varsY	{List.append $1 $3}
	|								{[]}
;

eqStmtsY:
		eqStmtY eqStmtsY	{$1::$2}
	|					{[]}
;

eqStmtY:
	    lhsLY EQ exprY SEMICOLON
		{EqStmt($1, $3)}
	|   lhsLY EQ simplFbyExprY SEMICOLON
        {EqStmt($1, $3)}
;

lhsLY:
		lhs COMMA lhsLY	{$1::$3}
	|	lhs				{[$1]}
	|   LPAREN lhsLY RPAREN {$2}
;

lhs:
		IDENT			{LVIdent { name = $1; key = intern_string $1 }}
    |   megaY           {LVMega $1}
;

megaY:
        MEGA DOT IDENT  {Mega ({ name = $1; key = intern_string $1}, { name = $3; key = intern_string $3})}
;

identsY:
		IDENT COMMA identsY	{{ name = $1; key = intern_string $1} :: $3}
	|	IDENT				{[{ name = $1; key = intern_string $1 }]}
;

atomExprY:
		IDENT		{EIdent { name = $1; key = intern_string $1 }}
	|	new_INT		{EInt { name = $1; key = Coq_xH }}
	|	new_REAL	{EReal { name = $1; key = Coq_xH }}
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
        atomExprY	    		    {CEAtom $1}
    |   constUnOpExprY      		{$1}
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

simplFbyExprY:
        exprsY FBY exprsY
		{FbyExpr(cons_exprlist $3, (CEAtom (EInt {name = "1"; key = intern_string "1" })), cons_exprlist $1)}
;

fbyExprY:
	    LPAREN exprsY FBY exprsY RPAREN
		{FbyExpr(cons_exprlist $4, (CEAtom (EInt {name = "1"; key = intern_string "1" })), cons_exprlist $2)}
;

whenExprY:
		exprY WHEN IDENT
			{WhenExpr($1, true, { name = $3; key = intern_string $3 })}
	|	exprY WHEN NOT IDENT
			{WhenExpr($1, false, { name = $4; key = intern_string $4 })}
;

ifExprY:
	IF exprY THEN exprY ELSE exprY
		{IfExpr($2, $4, $6)}
;

exprListY:
	exprsY
		{ExprList (cons_exprlist $1)}
;

callY:
	IDENT LPAREN exprsY RPAREN
		{Call({ name = $1; key = intern_string $1 }, cons_exprlist $3)}
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
	|	arrAccessExprY			{$1}
	|	arrInitExprY			{$1}
	|	arrConstructExprY		{$1}
	|	arrNameConstructExprY		{$1}
	|	PRE exprY	%prec	PREEXP	{PreExpr $2}
	|	CURRENT exprY			{CurrentExpr $2}
	|	fbyExprY			{$1}
	|	exprY ARROW exprY		{ArrowExpr($1, $3)}
	|	whenExprY			{$1}
	|	ifExprY				{$1}
	|	LPAREN exprListY RPAREN		{$2}
	|	callY			{$1}
	|	dieseExprY			{$1}
	|	norExprY			{$1}
    |   megaY       {MegaExpr $1}
;


new_INT:
		CONST_INT	{$1}
	|	ADD CONST_INT	{$2}
	|	MINUS CONST_INT {"-" ^ $2}
;

new_REAL:
		CONST_REAL	{$1}
	|	ADD CONST_REAL	{$2}
	|	MINUS CONST_REAL {"-" ^ $2}
;
