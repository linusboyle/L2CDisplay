open Display;;
open Util;;

let rec parse_display root =
    match root#node_type with
    | Pxp_document.T_element name ->
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
    | h1 :: h2 :: []  -> let res1 = parse_dis_main h1 in 
                        let res2 = parse_dis_main h2 in
                        begin match (res1, res2) with
                        | (Some d1, Some d2) -> if name = "hstack" then Some (Hstack (d1, d2)) else Some (Vstack (d1, d2))
                        | _ -> None 
                        end
    | _ -> None

and parse_dis_widget root name =
    let attrs = root#attributes in
    let rec find_text attrlist = 
        match attrlist with
        | [] -> None
        | (name, value) :: t -> if name = "text" then match value with
                                                    | Pxp_core_types.A.Value str -> Some str
                                                    | _ -> None
                                else find_text t
    in 
    match find_text attrs with
    | None -> None
    | Some str -> if name = "button" then Some (Button (coqstring_of_camlstring str))
                                     else Some (Label (coqstring_of_camlstring str))
