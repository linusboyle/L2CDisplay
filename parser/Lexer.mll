{

open Lexing
open Parser
open String
open Aut.GramDefs
exception Eof

}

rule token = parse
  | "short$"
    { get_token SHORTSSS'token }
  | "int$"
    { get_token INTSSS'token }
  | "float$"
    { get_token FLOATSSS'token }
  | "real$"
    { get_token REALSSS'token }
  | "not$"
    { get_token NOTSSS'token }
  | "+$"
    { get_token ADDSSS'token }
  | "-$"  
    { get_token MINUSSSS'token }
  | "$+$"  
    { get_token SSSADDSSS'token }
  | "$-$"  
    { get_token SSSMINUSSSS'token }
  | "$*$"  
    { get_token SSSMULSSS'token }
  | "$/$"  
    { get_token SSSDIVFSSS'token }
  | "$div$"  
    { get_token SSSDIVSSS'token }
  | "$mod$"  
    { get_token SSSMODSSS'token }
  | "$and$"  
    { get_token SSSANDSSS'token }
  | "$or$"  
    { get_token SSSORSSS'token }
  | "$xor$"  
    { get_token SSSXORSSS'token }
  | "$=$"      
    { get_token SSSEQSSS'token }
  | "$<>$"  
    { get_token SSSNESSS'token }
  | "$>$"      
    { get_token SSSGRESSS'token }
  | "$>=$"  
    { get_token SSSGREEQSSS'token }
  | "$<$"      
    { get_token SSSLESSSS'token }
  | "$<=$"  
    { get_token SSSLESEQSSS'token }
  | "^"    
    { get_token CARET'token }
  | ","
    { get_token COMMA'token }
  | ":"
    { get_token COLON'token }
  | ";"    
    { get_token SEMICOLON'token }
  | "+"
    { get_token ADD'token }
  | "-"
    { get_token MINUS'token }
  | "*"
    { get_token MUL'token }
  | "/"
    { get_token DIVF'token }
  | "="
    { get_token EQ'token }
  | "<>"
    { get_token NE'token }
  | "<"
    { get_token LES'token }
  | ">"
    { get_token GRE'token }
  | "<="
    { get_token LESEQ'token }
  | ">="
    { get_token GREEQ'token }
  | "->"
    { get_token ARROW'token }
  | "#"
    { get_token DIESE'token }
  | "_"
    { get_token DEFAULTPATTERN'token }
  | "|"
    { get_token SEG'token }
  | "."
    { get_token DOT'token }
  | "nor"
    { get_token NOR'token }
  | "not"
    { get_token NOT'token }
  | "div"
    { get_token DIV'token }
  | "mod"
    { get_token MOD'token }
  | "and"
    { get_token AND'token }
  | "or"
    { get_token OR'token }
  | "xor"
    { get_token XOR'token }
  | "("    
    { get_token LPAREN'token }
  | ")"    
    { get_token RPAREN'token }
  | "["    
    { get_token LBRACKET'token }
  | "]"    
    { get_token RBRACKET'token }
  | "{"    
    { get_token LBRACE'token }
  | "}"    
    { get_token RBRACE'token }
  | "type"  
    { get_token TYPE'token }
  | "const"
    { get_token CONST'token }
  | "function"  
    { get_token FUNCTION'token }
  | "node"    
    { get_token NODE'token }
  | "enum"
    { get_token ENUM'token }
  | "bool"  
    { get_token BOOL'token }
  | "ushort"  
    { get_token USHORT'token }
  | "short"  
    { get_token SHORT'token }
  | "uint"  
    { get_token UINT'token }
  | "int"    
    { get_token INT'token }
  | "real"  
    { get_token REAL'token }
  | "float"  
    { get_token FLOAT'token }
  | "char"  
    { get_token CHAR'token }
  | "true" as lxm
    { get_token (TRUE'token lxm) }
  | "false" as lxm
    { get_token (FALSE'token lxm) }
  | "var"
    { get_token VAR'token }
  | "let"
    { get_token LET'token }
  | "tel"
    { get_token TEL'token }
  | "returns"
    { get_token RETURNS'token }
  | "pre"
    { get_token PRE'token }
  | "fby"
    { get_token FBY'token }
  | "if"
    { get_token IF'token }
  | "then"
    { get_token THEN'token }
  | "else"
    { get_token ELSE'token }
  | "when"
    { get_token WHEN'token }
  | "case"
    { get_token CASE'token }
  | "of"
    { get_token OF'token }
  | "default"
    { get_token DEFAULT'token }
  | "with"
    { get_token WITH'token }
  | "boolred" 
    { get_token BOOLRED'token }
  | "map"  
    { get_token MAP'token }
  | "red"  
    { get_token RED'token }
  | "fill"  
    { get_token FILL'token }
  | "fillred"  
    { get_token FILLRED'token }
  | "merge"
    { get_token MERGE'token }
  | "current"
    { get_token CURRENT'token }
  | ['a'-'z''A'-'Z''_']['a'-'z''A'-'Z''0'-'9''_']* as lxm  
    { get_token (IDENT'token lxm) }
  | "\'"['a'-'z''A'-'Z''+''-']"\'" as lxm
    { get_token (CONST_CHAR'token (String.sub lxm 1 1)) }
  | ['0'-'9']+ "us" as lxm  
    { get_token (CONST_USHORT'token (String.sub lxm 0 (String.length lxm - 2))) }
  | ['0'-'9']+ "u" as lxm  
    { get_token (CONST_UINT'token (String.sub lxm 0 (String.length lxm - 1))) }
  | ['0'-'9']+ "s" as lxm  
    { get_token (CONST_SHORT'token (String.sub lxm 0 (String.length lxm - 1))) }
  | ['0'-'9']+ as lxm  
    { get_token (CONST_INT'token lxm) }
  | ['0'-'9']+ "." ['0'-'9']* "f" as lxm  
    { get_token (CONST_FLOAT'token (String.sub lxm 0 (String.length lxm - 1))) }
  | ['0'-'9']+ "." ['0'-'9']* as lxm  
    { get_token (CONST_REAL'token lxm) }
  | [' ' '\t' '\n' '\r' ]  
    { token lexbuf }     (* skip blanks *)
  | '/'[^'\n']*'*''/' 
    { token lexbuf }     (* skip blanks *)
  | "--"[^'\n']*      
    { token lexbuf } (* skip comment *)
  | [' ' '\t' '\n']+  
    { token lexbuf } (* skip spaces *)
  | "(*"              
    { comment lexbuf } (* activate "comment" rule *)
  | eof            
    { get_token EOF'token }
  | _              
    { print_string "unexpected token"; token lexbuf }
and comment = parse
  | "*)"      
    { token lexbuf } (* go to the "token" rule *)
  | _         
    { comment lexbuf } (* skip comments *)

{
  let token_stream lexbuf : token stream =
    let rec compute_token_stream () =
      let loop c_exist =
        Cons (c_exist, Lazy.from_fun compute_token_stream)
      in loop (token lexbuf)
    in Lazy.from_fun compute_token_stream
}
