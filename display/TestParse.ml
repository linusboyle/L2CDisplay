open Fileutil

let rec count_row content i j row oldi =
  if i < j then
    try 
      let i' = String.index_from content i '\n' in
      count_row content (i'+1) j (row+1) i
    with
      | _ -> (row, j - i)
  else
    (row, j - oldi)

let print_position outx lexbuf content =
  let curr = lexbuf.Lexing.lex_curr_p in
  (*let line = curr.Lexing.pos_lnum in*)
  let cnum = curr.Lexing.pos_cnum - curr.Lexing.pos_bol in
  let (line, col) = count_row content 0 cnum 0 0 in
  let tok = Lexing.lexeme lexbuf in
  Printf.fprintf outx "(line: %d,pos: %d, token: %s)" line col tok

let parser_by_ocaml content =
    let lexbuf = Lexing.from_string content in
    try        
        Display_parser.programY Display_lexer.token lexbuf
    with
    | Parsing.Parse_error ->
      let print_pos = fun std buf -> print_position std buf content in 
      Printf.fprintf stderr "%a\n" print_pos lexbuf;
      exit (-2)
;;

let parse_and_print fn =
  let lustre_content = read_whole_file fn in
  let ast = parser_by_ocaml lustre_content in
  print_string (PrintDisplay.lus_output ast)
;;

parse_and_print "test.lus";;
