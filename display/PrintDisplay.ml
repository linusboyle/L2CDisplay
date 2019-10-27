open Display
open Format
open Camlcoq

(*an (ugly) printer*)
let rec print_display p display =
    match display with
    | Button (text, click) ->
            let text_msg = 
                match text with
                |STconst id -> "with constant text '" ^ (extern_atom id) ^ "'"
                |STref (NRconstruct (nodename, slotname)) -> "with reference text to node " ^ (extern_atom nodename) ^ " and slot " ^ (extern_atom slotname)
            in
            let click_msg = 
                match click with
                |None -> ""
                |Some (NRconstruct (nodename, slotname)) -> "and with reference click signal to node " ^ (extern_atom nodename) ^ " and slot " ^ (extern_atom slotname)
            in
            fprintf p "a button %s %s\n" text_msg click_msg
    | Label text ->
            let text_msg = 
                match text with
                |STconst id -> "with constant text of '" ^ (extern_atom id) ^ "'"
                |STref (NRconstruct (nodename, slotname)) -> "with reference text to node " ^ (extern_atom nodename) ^ " and slot " ^ (extern_atom slotname)
            in
            fprintf p "a label %s\n" text_msg
    | Input (text, submit) ->
            let text_msg =
                match text with
                | None -> ""
                | Some (NRconstruct (nodename, slotname)) -> "with reference text signal to node " ^ (extern_atom nodename) ^ " and slot " ^ (extern_atom slotname)
            in
            let submit_msg =
                match submit with
                | None -> ""
                | Some (NRconstruct (nodename, slotname)) -> "with reference submit signal to node " ^ (extern_atom nodename) ^ " and slot " ^ (extern_atom slotname)
            in
            fprintf p "an input %s %s\n" text_msg submit_msg
    | Hstack (dis1,dis2) ->
            fprintf p "a hstack layout which contains:\n"; print_display p dis1; print_display p dis2
    | Vstack (dis1,dis2) -> 
            fprintf p "a vstack layout which contains:\n"; print_display p dis1; print_display p dis2
