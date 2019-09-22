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

let rec parse_display root =
    match root#node_type with
    | Pxp_document.T_element name ->
        (*should we check name = "display" here?*)
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
            else if name = "button" || name = "label" then
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
                      else parse_dis_button root

and parse_dis_label root =
    let properties = root#sub_nodes in
    match find_subnodes properties "text" with
    | None -> None
    | Some text_node -> 
            let data = get_data text_node in
            let ref = find_attributes text_node#attributes "ref" in
            match (data, ref) with
            | (None, _ ) -> None
            | (Some str, None) -> Some (Label (STconst (coqstring_of_camlstring str)) )
            | (Some str, Some nodename) -> Some (Label (STref (NRconstruct ((coqstring_of_camlstring nodename), (coqstring_of_camlstring str)) )))

and parse_dis_button root =
    let properties = root#sub_nodes in
    let text_node = find_subnodes properties "text" in
    let click_node = find_subnodes properties "click" in
    match (text_node, click_node) with
    | (None, _ ) -> None
    | (Some tn, None) -> 
            let data = get_data tn in
            let ref = find_attributes tn#attributes "ref" in
            begin match (data, ref) with
            | (None, _ ) -> None
            | (Some str, None) -> 
                    Some (Button ((STconst (coqstring_of_camlstring str)), None))
            | (Some str, Some nodename) -> 
                    Some (Button ((STref (NRconstruct (
                                    (coqstring_of_camlstring nodename), 
                                    (coqstring_of_camlstring str)
                                ))), None))
            end
    | (Some tn, Some cn) -> 
            let t_data = get_data tn in
            let t_ref = find_attributes tn#attributes "ref" in
            let c_data = get_data cn in
            let c_ref = find_attributes cn#attributes "ref" in
            begin match (t_data, t_ref, c_data, c_ref) with
            | (_ , _ , None, _) -> None
            | (_ , _ , _ , None) -> None
            | (None, _ , Some _, Some _) -> None
            | (Some str, None, Some c_slotname, Some c_nodename) -> 
                    Some (Button ((STconst (coqstring_of_camlstring str)), 
                            Some (NRconstruct (
                                    (coqstring_of_camlstring c_nodename), 
                                    (coqstring_of_camlstring c_slotname)
                            ))))
            | (Some t_slotname, Some t_nodename, Some c_slotname, Some c_nodename) -> 
                    Some (Button ((STref (NRconstruct (
                                    (coqstring_of_camlstring t_nodename), 
                                    (coqstring_of_camlstring t_slotname)
                                ))), 
                            Some (NRconstruct (
                                    (coqstring_of_camlstring c_nodename), 
                                    (coqstring_of_camlstring c_slotname)
                            ))))
            end
