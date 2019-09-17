open Display;;
open Util;;
open Format;;

let rec toXml d : coq_Xml =
    match d#node_type with
    | Pxp_document.T_element name ->
            toXml_element d name
    | Pxp_document.T_data ->
            XData (coqstring_of_camlstring d#data)
    | _ -> fprintf err_formatter "ill-formed input detected inside xml parser"; exit 1
and toXml_element d name : coq_Xml =
    let subnodes = d#sub_nodes in
    let subxmls = List.map toXml subnodes in
    let attrs = List.map 
        (fun (id, value) -> begin
            match value with
            |Pxp_core_types.A.Value str -> 
                    XAttr ((coqstring_of_camlstring id), (coqstring_of_camlstring str)) 
            |_ -> (fprintf err_formatter "Parsing has failed when processing attribute %s" id; exit 1)
            end)
        d#attributes 
    in
    XElement ((coqstring_of_camlstring name), attrs, subxmls)
;;
