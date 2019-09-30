open Display;;
open Util;;

let rec find_subnodes sublist nodename =
    match sublist with
    | [] -> None
    | h :: t -> match h#node_type with
                | Pxp_document.T_element hname ->
                        if hname = nodename then Some h
                        else find_subnodes t nodename
                | _ -> None

let rec find_attributes attrlist attrname =
    match attrlist with 
    | [] -> None
    | (name, value) :: t -> if name = attrname 
                            then match value with
                                | Pxp_core_types.A.Value str -> Some str 
                                | _ -> None
                            else find_attributes t attrname

let get_data node =
    match node#sub_nodes with
    | data_node :: [] ->
        begin match data_node#node_type with
        | Pxp_document.T_data ->
                Some data_node#data
        | _ -> None
        end
    | _ -> None

(* find output slot by name *)
let get_outputslot node slotname =
    let properties = node#sub_nodes in
    match find_subnodes properties slotname with
    | None -> None
    | Some slot_node -> 
        let data = get_data slot_node in
        let ref = find_attributes slot_node#attributes "ref" in
        match (data, ref) with
        | (None, _ ) -> None
        | (Some str, None) -> Some (STconst (coqstring_of_camlstring str))
        | (Some str, Some nodename) -> Some (STref (NRconstruct ((coqstring_of_camlstring nodename), (coqstring_of_camlstring str)) ))

(* find input slot by name *)
let get_inputslot node slotname =
    let properties = node#sub_nodes in
    match find_subnodes properties slotname with
    | None -> None
    | Some slot_node -> 
        let data = get_data slot_node in
        let ref = find_attributes slot_node#attributes "ref" in
        match (data, ref) with
        | (None, _ ) -> None
        | (_, None) -> None
        | (Some str, Some nodename) -> Some ((NRconstruct ((coqstring_of_camlstring nodename), (coqstring_of_camlstring str)) ))

let rec parse_display root =
    match root#node_type with
    | Pxp_document.T_element name ->
        (*shall we check name = "display" here?*)
        let subnodes = root#sub_nodes in
        begin match subnodes with
        | node :: [] -> parse_dis_main node
        | _ -> None
        end
    | _ -> None

and parse_dis_main root =
    match root#node_type with
    | Pxp_document.T_element name ->
            if name = "hstack" || name = "vstack" then
                parse_dis_layout root name
            else if name = "button" || name = "label" 
                    || name = "input"
            then
                parse_dis_widget root name
            else None
    | _ -> None

and parse_dis_layout root name =
    let subnodes = root#sub_nodes in
    match subnodes with
    | h1 :: h2 :: [] -> let res1 = parse_dis_main h1 in 
                        let res2 = parse_dis_main h2 in
                        begin match (res1, res2) with
                        | (Some d1, Some d2) -> if name = "hstack" then Some (Hstack (d1, d2)) else Some (Vstack (d1, d2))
                        | _ -> None 
                        end
    | _ -> None

and parse_dis_widget root name =
    if name = "label" then parse_dis_label root
    else if name = "button" then parse_dis_button root
    else parse_dis_input root

and parse_dis_label root =
    match get_outputslot root "text" with
    | None -> None
    | Some slot -> Some (Label slot)

and parse_dis_button root =
    match ((get_outputslot root "text"), (get_inputslot root "click")) with
    | (None, _) -> None
    | (Some textslot, clickslot) -> Some (Button (textslot, clickslot))

and parse_dis_input root = 
    Some (Input ((get_inputslot root "inputtext"), (get_inputslot root "submit")))
