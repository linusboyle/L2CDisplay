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

open Arg
open Version

let usage_msg="\
USAGE:	l2c [options] <source.ast>

options:
";;

let flag_save_temp = ref false;;
let flag_ctemp = ref false;;
let target_dir = ref "";;
let output_file = ref "";;
let flag_print_parse = ref false;;
let display_file = ref "";;
let flag_print_display = ref false;;

let options = [
    ("-save-temp", Set flag_save_temp, "    Save temporary immediate files");
    ("-ctemp", Set flag_ctemp, "    Output ctemp source");
    ("-print-parse", Set flag_print_parse, "    Print parse output");
    ("-display", Set_string display_file, "<file> The specification file of the l2c display mode");
    ("-print-display", Set flag_print_display, "    Print parsed output of display model");
    ("-target_dir", Set_string target_dir, "<dir>    The directory of generated target files");
    ("-o", Set_string output_file, "<file>    Indicate the output file name");
    ("-version", Unit (fun()->(print_string version_msg)), "    Print version information");
    ("-help", Unit (fun()->(print_string usage_msg)), " Print this usage message");
];;
