(* *********************************************************************)
(*                                                                     *)
(*              The L2C verified compiler                              *)
(*                                                                     *)
(*            L2C Group, Tsinghua University                           *)
(*                                                                     *)
(*  Copyright Tsinghua University.  All rights reserved.  This file is *)
(*  distributed under the terms of the GNU General Public License as   *)
(*  published by the Free Software Foundation, either version 2 of the *)
(*  License, or (at your option) any later version.  This file is also *)
(*  distributed under the terms of the INRIA Non-Commercial License    *)
(*  Agreement.                                                         *)
(*                                                                     *)
(* *********************************************************************)

open Fileutil
open Camlcoq
open Printf
open Options
open Format
open AST
open PrintClight
open Datatypes
open BinPos
open ParseDisplay
open PrintDisplay

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


let parser_by_ocaml content =
    let lexbuf = Lexing.from_string content in
    try        
        Ocaml_parser.programY Ocaml_lexer.token lexbuf
    with
    | Parsing.Parse_error ->
      let print_pos = fun std buf -> print_position std buf content in 
      Printf.fprintf stderr "%a\n" print_pos lexbuf;
      exit (-2)
;;

let parser_by_coq content =
  let rec inf = Parser.S inf in
  let lexbuf = Lexing.from_string content in
  let parsing_result = Parser.p_Program inf (Lexer.token_stream lexbuf) in
  (
    match parsing_result with
    | Parser.Parser.Inter.Fail_pr ->
      print_string "Parsing Failed!\n";
      exit (-2)
    | Parser.Parser.Inter.Timeout_pr ->
      print_string "Timed Out!\n";
      exit (-3)
    | Parser.Parser.Inter.Parsed_pr (output, _) ->
      let abstract_syntax_tree : Tree.program = Obj.magic output in
        abstract_syntax_tree
  )
;;

let parser_display_mode fn =
    let dis_model = parse_display_from_file fn in
    match dis_model with
    | None -> print_string "Display mode has been bypassed because of error\n"; None
    | Some model -> 
        if !flag_print_display then print_display std_formatter model else ();
        let astC = DisplayClightGen.trans_program model in
        Some astC
;;

let translate fn=
  let mfn = fn in
  let lustre_content = read_whole_file fn in
  let ast = if !flag_coq_parser then parser_by_coq lustre_content else parser_by_ocaml lustre_content in

  if !flag_print_parse then print_string (PrintTree.lus_output ast) else ();

  let ast' = 
    match TransTypeName.trans_program ast with
    | Errors.OK p -> p
    | Errors.Error msg ->
        print_error stderr msg;
	exit 2 in

  let (main, asti) =
    match LustreWGen.trans_program ast' with
    | Errors.OK p -> p
    | Errors.Error msg ->
        print_error stderr msg;
	exit 2 in

  let astV =
    match LustreVGen.trans_program asti with
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

  let astC_dis = if !display_file = "" then None else parser_display_mode !display_file in

  let () = 
    match astC_dis with
    | None -> ()
    | Some astC -> output_c_file astC (path ^ "_display")
  in

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
  else output_c_file astC path;
  ;;

let parse_command () =
    if (Array.length Sys.argv)=1 then
      print_string usage_msg
    else
      Arg.parse (Arg.align options) translate usage_msg;;

parse_command ();;
