open Parse
open Display
open Util
open Format

(*simple driver*)
let spec = Pxp_tree_parser.default_spec
let config = Pxp_types.default_config
let source = Pxp_types.from_file "test.xml"

let () = 
    let doc = 
        try
            Pxp_tree_parser.parse_document_entity config source spec 
        with
        | Pxp_types.Validation_error _
        | Pxp_types.WF_error _
        | Pxp_types.Namespace_error _
        | Pxp_types.Error _
        | Pxp_types.At(_,_) as error ->
            print_endline ("PXP error " ^ Pxp_types.string_of_exn error);exit 1
    in
    let rec print_display display =
        match display with
        | Button (text, click) ->
                let text_msg = 
                    match text with
                    |STconst const_text -> "with constant text of '" ^ (camlstring_of_coqstring const_text) ^ "'"
                    |STref (NRconstruct (nodename, slotname)) -> "with reference text to node " ^ (camlstring_of_coqstring nodename) ^ " and slot " ^ (camlstring_of_coqstring slotname)
                in
                let click_msg = 
                    match click with
                    |None -> ""
                    |Some (NRconstruct (nodename, slotname)) -> "and with reference click signal to node " ^ (camlstring_of_coqstring nodename) ^ " and slot " ^ (camlstring_of_coqstring slotname)
                in
                fprintf std_formatter "a button %s %s\n" text_msg click_msg
        | Label text ->
                let text_msg = 
                    match text with
                    |STconst const_text -> "with constant text of '" ^ (camlstring_of_coqstring const_text) ^ "'"
                    |STref (NRconstruct (nodename, slotname)) -> "with reference text to node " ^ (camlstring_of_coqstring nodename) ^ " and slot " ^ (camlstring_of_coqstring slotname)
                in
                fprintf std_formatter "a label %s\n" text_msg
        | Hstack (dis1,dis2) ->
                fprintf std_formatter "a hstack layout which contains:\n"; print_display dis1; print_display dis2
        | Vstack (dis1,dis2) -> 
                fprintf std_formatter "a vstack layout which contains:\n"; print_display dis1; print_display dis2
    in
    let parsed = parse_display doc#root in
    match parsed with
    | None -> print_endline "Parsing error"
    | Some display ->
        print_display display
