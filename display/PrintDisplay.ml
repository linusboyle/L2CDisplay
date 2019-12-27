(* File main.ml *)
open BinNums
open LDisplay
open Camlcoq

let indent depth str = Printf.sprintf "%s%s" (String.make (depth * 4) ' ') str

let to_int i = P.to_int i

let lus_identOut id =
    Printf.sprintf "(%s, %d)" id.name (to_int id.key)

let rec lus_atomExprOut = function
  | EIdent id -> id.name
  | EBool id -> id.name
  | EInt id -> id.name
  | EReal id -> id.name

let lus_unopOut = function
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
  | AtomType Int -> "int"
  | AtomType Real -> "real"
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
  | ArrAccessExpr (e1, e2) -> Printf.sprintf "%s[%s]" (lus_exprOut e1) (lus_constExprOut e2)
  | ArrInitExpr (e1, e2) -> Printf.sprintf "%s^%s" (lus_exprOut e1) (lus_constExprOut e2)
  | ArrConstructExpr el -> Printf.sprintf "[%s]" (lus_listExprOut el)
  | NameConstructExpr nl -> Printf.sprintf "{%s}" (lus_nameConstructExprOut nl)
  | PreExpr e -> Printf.sprintf "pre(%s)" (lus_exprOut e)
  | FbyExpr (el1, i, el2) -> Printf.sprintf "fby(%s; %s; %s)" (lus_listExprOut el1) (lus_constExprOut i) (lus_listExprOut el2)
  | ArrowExpr (e1, e2) ->  Printf.sprintf "%s -> %s" (lus_exprOut e1) (lus_exprOut e2)
  | WhenExpr (e1, ckb, id) -> Printf.sprintf "%s when %s %s" (lus_exprOut e1) (if ckb then "" else "not") id.name
  | CurrentExpr e -> Printf.sprintf "current(%s)" (lus_exprOut e)
  | IfExpr (e1, e2, e3) -> Printf.sprintf "if %s then %s else %s)" (lus_exprOut e1) (lus_exprOut e2) (lus_exprOut e3)
  | ExprList el -> "(" ^ (lus_listExprOut el) ^ ")"
  | Call (id, el) -> Printf.sprintf "%s(%s)" (id.name) (lus_listExprOut el)
  | DieseExpr e -> Printf.sprintf "#(%s)" (lus_exprOut e)
  | NorExpr e -> Printf.sprintf "nor(%s)" (lus_exprOut e)
  | MergeExpr (id, e1, e2) -> Printf.sprintf "merge(%s, %s, %s)" id.name (lus_exprOut e1) (lus_exprOut e2)

and lus_nameConstructExprOut = function
  | NamesNil -> ""
  | NamesCons (id, e, NamesNil) -> Printf.sprintf "%s: %s" id.name (lus_exprOut e)
  | NamesCons (id, e, nl) -> Printf.sprintf "%s: %s, %s" id.name (lus_exprOut e) (lus_nameConstructExprOut nl)

and lus_listExprOut = function
  | Enil -> ""
  | Econs (c, Enil) -> lus_exprOut c
  | Econs (c, cl) -> Printf.sprintf "%s, %s" (lus_exprOut c) (lus_listExprOut cl)

let lus_rhsOut = function
    | RVMega (Mega (wgt, field)) -> Printf.sprintf "$%s.%s" wgt.name field.name
    | RVExpr e -> lus_exprOut e

let lus_lhsOut = function
    | LVMega (Mega (wgt, field)) -> Printf.sprintf "$%s.%s" wgt.name field.name
    | LVIdent ids -> String.concat ", " (names_of_idents ids)

let lus_eqOut = function
    EqStmt (lhs, rhs) ->
      Printf.sprintf "%s = %s" (indent 2 (lus_lhsOut lhs)) (lus_rhsOut rhs)

let lus_eqsOut eqs =
  String.concat "\n" [
      indent 1 "Equations";
      String.concat "\n" (List.map lus_eqOut eqs)
  ]

let lus_staticOut depth field = match field with
   (id, k) -> 
      Printf.sprintf "%s: %s" (indent depth (lus_identOut id)) (kindOut k)

let lus_fieldOut depth field = match field with
   ((id, k), ck) -> 
      Printf.sprintf "%s: %s %s" (indent depth (lus_identOut id)) (kindOut k) (clockOut ck)

let lus_varsOut = function
    fields ->
        if List.length fields = 0 then "" else
        String.concat "\n" 
        [
            indent 1 "Vars";
            String.concat "\n" (List.map (lus_fieldOut 2) fields)
        ]


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
  | WidgetBlk (id, st, pl, retl) ->
    String.concat "\n" 
    [   indent 0 "Widget";
        indent 1 (lus_identOut id);
        indent 1 "Params";
        String.concat "\n" (List.map (lus_staticOut 2) st);
        indent 1 "Params";
        String.concat "\n" (List.map (lus_fieldOut 2) pl);
        indent 1 "Events";
        String.concat "\n" (List.map (lus_fieldOut 2) retl);
    ]
  | ControlBlk (id, body) ->
    String.concat "\n" 
    [   indent 0 "Control";
        indent 1 (lus_identOut id);
        lus_bodyOut body
    ]

let lus_output = function 
  | nodes -> String.concat "\n\n" (List.map lus_nodeOut nodes)
