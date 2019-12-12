{
    open Display_parser
    exception Eof
}

let ident_rexp = ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']*

rule token = parse
	[' ' '\t' '\n' '\r' ] { token lexbuf }     (* skip blanks *)
	| '/'[^'\n']*'*''/'   { token lexbuf }     (* skip blanks *)

	| "type"              { TYPE }
	| "function"          { FUNCTION }
	| "widget"          { WIDGET }
	| "ctrl"          { CTRL }
	| "node"              { NODE }
	| "returns"           { RETURNS }
	| "let"               { LET }
	| "tel"               { TEL }
	| "var"               { VAR }
	| "const"             { CONST }
	| "pre"               { PRE }
	| "fby"               { FBY }
	| "if"                { IF }
	| "then"              { THEN }
	| "else"              { ELSE }
	| "when"              { WHEN }
	| "current"           { CURRENT }
	| "merge"             { MERGE }
	| "->"                { ARROW }
	| "enum"              { ENUM }

    | '$'(ident_rexp as lxm)   { MEGA (lxm) }

	| "not" { NOT }
	| "+"   { ADD }
	| "-"   { MINUS }
	| "*"   { MUL }
	| "/"   { DIVF }
	| "div" { DIV }
	| "mod" { MOD }
	| "and" { AND }
	| "or"  { OR }
	| "xor" { XOR }
	| "<="  { LESEQ }
	| ">="  { GREEQ }
	| "<>"  { NE }
	| "="   { EQ }
	| "<"   { LES }
	| ">"   { GRE }

	| "#"       { DIESE }
	| "nor"     { NOR }

	(*| "char"	{ CHAR }*)
	| "bool"	{ BOOL }
	(*| "ushort"	{ USHORT }*)
	(*| "short"	{ SHORT }*)
	(*| "uint"	{ UINT }*)
	| "int"		{ INT }
	| "real"	{ REAL }
	(*| "float"	{ FLOAT }*)

	| "true" 			{ TRUE }
	| "false"			{ FALSE }
	(*| ['0'-'9']+ "us" as lxm	{ CONST_USINT (String.sub lxm 0 (String.length lxm - 2)) }*)
	(*| ['0'-'9']+ 'u' as lxm	{ CONST_UINT (String.sub lxm 0 (String.length lxm - 1)) }*)
	(*| ['0'-'9']+ 's' as lxm	{ CONST_SINT (String.sub lxm 0 (String.length lxm - 1)) }*)
	| ['0'-'9']+ as lxm	{ CONST_INT lxm }
	(*| ['0'-'9']+ '.' ['0'-'9']* 'f' as lxm	{ CONST_FLO (String.sub lxm 0 (String.length lxm - 1)) }*)
	| ['0'-'9']+ '.' ['0'-'9']* as lxm	{ CONST_REAL lxm }
	(*| '\''['a'-'z''A'-'Z''+''-']'\'' as lxm	{ CONST_CHAR (String.sub lxm 1 1) }*)
    | ident_rexp as lxm	{ IDENT (lxm) }

	| '('		{ LPAREN }
	| ')'		{ RPAREN }
    | ','       { COMMA  }
    | ':'		{ COLON }
    | ';'		{ SEMICOLON }
    | '^'		{ CARET }
    | '['		{ LBRACKET }
    | ']'		{ RBRACKET }
    | '{'		{ LBRACE }
    | '}'		{ RBRACE }
    | '.'		{ DOT }

    | "--"[^'\n']*     { token lexbuf } (* skip comment *)
    | [' ' '\t' '\n']+ { token lexbuf } (* skip spaces *)
    | "(*"             { comment lexbuf } (* activate "comment" rule *)
  	| eof              { EOF }
    | _                { print_string "unexpected token"; token lexbuf}

and comment = parse
    | "*)"      { token lexbuf } (* go to the "token" rule *)
    | _         { comment lexbuf } (* skip comments *)
