(* File main.ml *)
open BinNums
open Tree

let indent depth str = Printf.sprintf "%s%s" (String.make (depth * 4) ' ') str

let rec to_int i = match i with
  | BinNums.Coq_xI p -> let n = to_int p in n + n + 1
  | BinNums.Coq_xO p -> let n = to_int p in n + n
  | BinNums.Coq_xH -> 1

let lus_identOut id =
    Printf.sprintf "(%s, %d)" id.name (to_int id.key)

let rec lus_atomExprOut = function
  | EIdent id -> id.name
  | EBool id -> id.name
  | EChar id -> id.name
  | EShort id -> id.name
  | EUShort id -> id.name
  | EInt id -> id.name
  | EUInt id -> id.name
  | EFloat id -> id.name
  | EReal id -> id.name

let lus_unopOut = function
    | AtomTypeOp Bool -> "bool"
    | AtomTypeOp Short -> "short"
    | AtomTypeOp UShort -> "ushort"
    | AtomTypeOp Int -> "int"
    | AtomTypeOp UInt -> "uint"
    | AtomTypeOp Float -> "float"
    | AtomTypeOp Real -> "real"
    | AtomTypeOp Char -> "char"
    | NOT -> "not"
    | POS -> "+"
    | NEG -> "-"

let lus_binopOut = function
    | ADD -> "+"
    | SUB -> "-"
    | MUL -> "*"
    | DIVF -> "/"
    | DIV -> "div"
    | MOD -> "mod"
    | AND -> "and"
    | OR -> "or"
    | XOR -> "xor"
    | GT -> ">"
    | LT -> "<"
    | GE -> ">="
    | LE -> "<="
    | EQ -> "="
    | NE -> "<>"

let lus_prefixUnOpOut = function
    | PSHORT -> "short$"
    | PINT -> "int$"
    | PFLOAT -> "float$"
    | PREAL -> "real$"
    | PNOT -> "not$"
    | PPOS -> "+$"
    | PNEG -> "-$"

let lus_prefixBinOpOut = function
    | ADD -> "$+$"
    | SUB -> "$-$"
    | MUL -> "$*$"
    | DIVF -> "$/$"
    | DIV -> "$div$"
    | MOD -> "$mod$"
    | AND -> "$and$"
    | OR -> "$or$"
    | XOR -> "$xor$"
    | GT -> "$>$"
    | LT -> "$<$"
    | GE -> "$>=$"
    | LE -> "$<=$"
    | EQ -> "$=$"
    | NE -> "$<>$"

let lus_highOrderOpOut = function
    | MAP -> "map"
    | RED -> "red"
    | FILL -> "fill"
    | FILLRED -> "fillred"

let lus_patternOut = function
  | PIdent id -> id.name
  | PBool id -> id.name
  | PChar id -> id.name
  | PInt id -> id.name
  | DefaultPattern -> "_"

let lus_prefixOpOut = function
  | Ident id -> id.name
  | UnOp o -> lus_prefixUnOpOut o
  | BinOp o -> lus_prefixBinOpOut o

let rec lus_constExprOut = function
  | CEAtom a -> lus_atomExprOut a
  | CEUnOpExpr (op, e1) -> Printf.sprintf "(%s %s)" (lus_unopOut op) (lus_constExprOut e1)
  | CEBinOpExpr (op, e1, e2) -> Printf.sprintf "(%s %s %s)" (lus_constExprOut e1) (lus_binopOut op) (lus_constExprOut e2)
  | CEConstructor items -> Printf.sprintf "{%s}" (lus_cnameItemsOut items)
  | CEArray cl -> Printf.sprintf "[%s]" (lus_constExprlistOut cl)

and lus_constExprlistOut = function
  | CEnil -> ""
  | CEcons (c, CEnil) -> lus_constExprOut c
  | CEcons (c, cl) -> Printf.sprintf "%s, %s" (lus_constExprOut c) (lus_constExprlistOut cl)

and lus_cnameItemsOut = function
  | CNamesNil -> ""
  | CNamesCons (id, c, CNamesNil) -> Printf.sprintf "%s: %s" id.name (lus_constExprOut c)
  | CNamesCons (id, c, nl) -> Printf.sprintf "%s: %s, %s" id.name (lus_constExprOut c) (lus_cnameItemsOut nl)

let clockOut = function
  | Clock (ckb, ckid) -> Printf.sprintf "when %s %s" (if ckb then "" else "not") ckid.name
  | NOCLOCK -> ""

let names_of_idents idents =
  List.map (fun id -> id.name) idents

let rec kindOut = function
  | AtomType Bool -> "bool"
  | AtomType Short -> "short"
  | AtomType UShort -> "ushort"
  | AtomType Int -> "int"
  | AtomType UInt -> "uint"
  | AtomType Float -> "float"
  | AtomType Real -> "real"
  | AtomType Char -> "char"
  | EnumType idents -> Printf.sprintf "enum{%s}" (String.concat ", " (names_of_idents idents))
  | Struct cons -> Printf.sprintf "struct{%s}" (fieldsOut cons)
  | Array (kind, len) -> Printf.sprintf "array(%s, INT(%s))" (kindOut kind) (lus_constExprOut len)
  | TypeDef ident -> Printf.sprintf "typename(%s)" (ident.name)

and fieldsOut = function
  | Fnil -> ""
  | Fcons (is, k, Fnil) -> Printf.sprintf "%s: %s" is.name (kindOut k)
  | Fcons (is, k, ftl) -> Printf.sprintf "%s: %s, %s" is.name (kindOut k) (fieldsOut ftl)


let rec lus_exprOut = function
  | AtomExpr ae -> lus_atomExprOut ae
  | UnOpExpr (op, e) -> Printf.sprintf "(%s %s)" (lus_unopOut op) (lus_exprOut e)
  | BinOpExpr (op, e1, e2) -> Printf.sprintf "(%s %s %s)" (lus_exprOut e1) (lus_binopOut op) (lus_exprOut e2)
  | FieldExpr (e, id) -> Printf.sprintf "%s.%s" (lus_exprOut e) id.name
  | DynamicProjectExpr (e1, el, e2) -> Printf.sprintf "(%s.%s default %s)" (lus_exprOut e1) (lus_dynamicListOut el) (lus_exprOut e2)
  | ArrAccessExpr (e1, e2) -> Printf.sprintf "%s[%s]" (lus_exprOut e1) (lus_constExprOut e2)
  | ArrInitExpr (e1, e2) -> Printf.sprintf "%s^%s" (lus_exprOut e1) (lus_constExprOut e2)
  | ArrConstructExpr el -> Printf.sprintf "[%s]" (lus_listExprOut el)
  | NameConstructExpr nl -> Printf.sprintf "{%s}" (lus_nameConstructExprOut nl)
  | PreExpr e -> Printf.sprintf "pre(%s)" (lus_exprOut e)
  | FbyExpr (el1, i, el2) -> Printf.sprintf "fby(%s; %s; %s)" (lus_listExprOut el1) (lus_constExprOut i) (lus_listExprOut el2)
  | ArrowExpr (e1, e2) ->  Printf.sprintf "%s -> %s" (lus_exprOut e1) (lus_exprOut e2)
  | WhenExpr (e1, ckb, id) -> Printf.sprintf "%s when %s %s" (lus_exprOut e1) (if ckb then "" else "not") id.name
  | CurrentExpr e -> Printf.sprintf "current(%s)" (lus_exprOut e)
  | MergeExpr (id, e1, e2) -> Printf.sprintf "merge(%s, %s, %s)"  id.name (lus_exprOut e1) (lus_exprOut e2)
  | IfExpr (e1, e2, e3) -> Printf.sprintf "if %s then %s else %s)" (lus_exprOut e1) (lus_exprOut e2) (lus_exprOut e3)
  | CaseExpr (e1, cl) -> Printf.sprintf "(case %s of %s)" (lus_exprOut e1) (lus_caseListOut cl)
  | NameWithExpr (id, wl, e) ->
    Printf.sprintf "(%s with %s = %s)" id.name (lus_nameWithListOut wl) (lus_exprOut e)
  | ExprList el -> lus_listExprOut el
  | PrefixExpr (op, el) -> Printf.sprintf "%s(%s)" (lus_prefixOpOut op) (lus_listExprOut el)
  | HighOrderExpr (hop, pop, i, el) ->
    Printf.sprintf "%s<<%s; %s>>(%s)" (lus_highOrderOpOut hop) (lus_prefixOpOut pop) (lus_constExprOut i) (lus_listExprOut el)
  | BoolredExpr (i1, i2, e) -> Printf.sprintf "boolred<<%s, %s>>(%s)" i1 i2 (lus_exprOut e)
  | DieseExpr e -> Printf.sprintf "#(%s)" (lus_exprOut e)
  | NorExpr e -> Printf.sprintf "nor(%s)" (lus_exprOut e)

and lus_nameWithListOut = function
  | WithNil -> ""
  | WithCons (FieldItem id, wl) -> Printf.sprintf ".%s%s" id.name (lus_nameWithListOut wl) 
  | WithCons (AccessItem e, wl) ->  Printf.sprintf "[%s]%s" (lus_exprOut e) (lus_nameWithListOut wl) 

and lus_dynamicListOut = function
  | Enil -> ""
  | Econs (e, el) -> Printf.sprintf "[%s]%s" (lus_exprOut e) (lus_dynamicListOut el)

and lus_nameConstructExprOut = function
  | NamesNil -> ""
  | NamesCons (id, e, NamesNil) -> Printf.sprintf "%s: %s" id.name (lus_exprOut e)
  | NamesCons (id, e, nl) -> Printf.sprintf "%s: %s, %s" id.name (lus_exprOut e) (lus_nameConstructExprOut nl)

and lus_caseListOut = function
  | CasesNil -> ""
  | CasesCons (p, e, cl) -> Printf.sprintf "| %s : %s %s" (lus_patternOut p) (lus_exprOut e) (lus_caseListOut cl)

and lus_listExprOut = function
  | Enil -> ""
  | Econs (c, Enil) -> lus_exprOut c
  | Econs (c, cl) -> Printf.sprintf "%s, %s" (lus_exprOut c) (lus_listExprOut cl)

let lus_eqOut = function
    EqStmt (lhsl, e) -> 
      Printf.sprintf "%s = %s" (indent 2 (String.concat " " (names_of_idents lhsl))) (lus_exprOut e)

let lus_eqsOut eqs =
  String.concat "\n" [
      indent 1 "Equations";
      String.concat "\n" (List.map lus_eqOut eqs)
  ]

let lus_fieldOut depth field = match field with
   ((id, k), ck) -> 
      Printf.sprintf "%s: %s %s" (indent depth (lus_identOut id)) (kindOut k) (clockOut ck)

let lus_varsOut = function
  | VarList fields ->
     String.concat "\n" [
         indent 1 "Vars";
         String.concat "\n" (List.map (lus_fieldOut 2) fields)
     ]
  | NOVARBLK -> ""


let lus_bodyOut = function
    BodyBlk (vars, eqs) ->
    String.concat "\n" [
        lus_varsOut vars;
        lus_eqsOut eqs
    ]

let lus_csStmtOut = function
    ConstStmt (id, k, e) -> 
      Printf.sprintf "%s: %s = %s" (indent 1 id.name) (kindOut k) (lus_constExprOut e)

let lus_tyStmtOut = function
    TypeStmt (id, k) ->
     Printf.sprintf "%s = %s" (indent 1 id.name) (kindOut k)

let lus_nodeOut = function
  | TypeBlk tyl ->
     String.concat "\n" [
         indent 0 "Type";
         String.concat "\n" (List.map lus_tyStmtOut tyl)
     ]
  | ConstBlk csl ->
     String.concat "\n" [
         indent 0 "Const";
         String.concat "\n" (List.map lus_csStmtOut csl)
     ]
  | FuncBlk (ft, id, pl, retl, body) ->
     String.concat "\n" [
         indent 0 "Function";
         indent 1 (lus_identOut id);      
         indent 1 "Params";
         String.concat "\n" (List.map (lus_fieldOut 2) pl);
         indent 1 "Return";
         String.concat "\n" (List.map (lus_fieldOut 2) retl);
         lus_bodyOut body
     ]

let rec lus_output = function 
  | nodes -> String.concat "\n\n" (List.map lus_nodeOut nodes)






    











