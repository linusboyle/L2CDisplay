open Fileutil
open Camlcoq
open Printf
open Options
open Format
open AST
open PrintClight
open Datatypes
open BinPos

let print_error oc msg =
  let print_one_error = function
  | Errors.MSG s -> output_string oc (Camlcoq.camlstring_of_coqstring s)
  | Errors.CTX i -> output_string oc (Camlcoq.extern_atom i)
  | Errors.POS i -> output_string oc (Camlcoq.extern_atom i)
  in
    List.iter print_one_error msg;
    output_char oc '\n'

let set_target_dir_path fn =
    let mfn=Filename.basename (Filename.chop_extension fn) in
    let dirmfn=Filename.dirname fn in
    let fullpath=dirmfn ^ "/" ^ mfn in
    if !target_dir="" then fullpath
    else mfn
    ;;

let output_path main mfn=
    let fn=set_target_dir_path mfn in
    let fn =
      if !output_file="" then (Filename.concat !target_dir fn)
      else if (Filename.is_implicit !output_file) then (Filename.concat !target_dir !output_file)
      else !output_file in

    let str_node =
       if !output_file = "" then extern_atom main
       else Filename.basename (Filename.chop_extension !output_file) in

    Filename.concat (Filename.dirname (fn ^ ".ast")) (str_node)
    ;;

let output_c_file prog path=
    let channel = open_out (path ^ ".c") in
    print_program (formatter_of_out_channel channel) prog;
    close_out channel;
  ;;

ignore (intern_string "acg_global_clock");; (*1*)
ignore (intern_string "acg_global_2");; (*2*)
ignore (intern_string "acg_global_3");; (*3*)
ignore (intern_string "acg_global_4");; (*4*)
ignore (intern_string "acg_global_5");; (*5*)
ignore (intern_string "acg_global_6");; (*6*)
ignore (intern_string "outC");; (*7*)
ignore (intern_string "acg_j");; (*8*)
ignore (intern_string "idx");; (*9*)
ignore (intern_string "items");; (*10*)
ignore (intern_string "inC");; (*11*)
ignore (intern_string "acg_i");; (*12*)
ignore (intern_string "acg_b");; (*13*)
ignore (intern_string "acg_local");; (*14*)
ignore (intern_string "acg_c1");; (*15*)
ignore (intern_string "acg_c2");; (*16*)
ignore (intern_string "acg_equ");; (*17*)
ignore (intern_string "acg_init");; (*18*)

exception SyntaxError of string

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

let parse_ldisplay content =
    let lexbuf = Lexing.from_string content in
    try        
        Display_parser.programY Display_lexer.token lexbuf
    with
    | Parsing.Parse_error ->
      let print_pos = fun std buf -> print_position std buf content in 
      Printf.fprintf stderr "%a\n" print_pos lexbuf;
      exit (-2)
;;

let translate fn=
  let mfn = fn in
  let lustre_content = read_whole_file fn in
  let ast = parse_ldisplay lustre_content in

  if !flag_print_parse then print_string (PrintDisplay.lus_output ast) else ();

  let markup = 
      match ParseXml.parse_from_file (!display_file) with
      | None -> exit 2
      | Some xml -> xml
  in

  let ast' = 
    match TransType.trans_program ast with
    | Errors.OK p -> p
    | Errors.Error msg ->
        print_error stderr msg;
	exit 2 in

  let (main, asti) =
    match DisplayWGen.trans_program ast' with
    | Errors.OK p -> p
    | Errors.Error msg ->
        print_error stderr msg;
	exit 2 in

  let (astw, extinfo) =
    match LustreWGenDis.trans_program asti markup with
    | Errors.OK p -> p
    | Errors.Error msg ->
        print_error stderr msg;
	exit 2 in

  let astV =
    match LustreVGen.trans_program astw with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in

  let astS =
    match LustreSGen.trans_program astV with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in

  let path = output_path main mfn in

  let set_dest dst opt f =
    dst := if !opt then Some f
                   else None in
  set_dest PrintLustreS.destination_t flag_save_temp (path ^ ".lust");
  set_dest PrintLustreS.destination_s flag_save_temp (path ^ ".luss");
  set_dest PrintLustreR.destination_r1 flag_save_temp (path ^ ".lusr1");
  set_dest PrintLustreR.destination_r2 flag_save_temp (path ^ ".lusr2");
  set_dest PrintLustreR.destination_r3 flag_save_temp (path ^ ".lusr3");
  set_dest PrintLustreF.destination_f1 flag_save_temp (path ^ ".lusf1");
  set_dest PrintLustreF.destination_f2 flag_save_temp (path ^ ".lusf2");
  set_dest PrintLustreF.destination_e1 flag_save_temp (path ^ ".luse1");
  set_dest PrintLustreF.destination_e2 flag_save_temp (path ^ ".luse2");
  set_dest PrintLustreF.destination_d flag_save_temp (path ^ ".lusd");
  set_dest PrintLustreF.destination_c flag_save_temp (path ^ ".lusc");

  set_dest PrintCtemp.destination flag_ctemp (path ^ ".c");

  let astC =
    match Compiler.transf_lt_program astS with
    | Errors.OK x -> x
    | Errors.Error msg ->
        print_error stderr msg;
        exit 2 in
  (* Print Clight *)
  if !flag_ctemp then ()
  else output_c_file astC path
  ;;

let parse_command () =
    if (Array.length Sys.argv)=1 then
      Arg.usage (Arg.align options) usage_msg
    else
      Arg.parse (Arg.align options) translate usage_msg;;

parse_command ();;
