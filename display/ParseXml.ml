open Camlcoq
open MarkUp

let is_element node =
    match node#node_type with
    | Pxp_document.T_element _ -> true
    | _ -> false

let rec parse_id attrs =
    match attrs with
    | [] -> None
    | (name, value) :: t ->
        let ta = parse_id t in
        match value with
        | Pxp_core_types.A.Value str -> 
            if name = "id" then 
                match ta with
                | None -> Some (intern_string str)
                | Some _ -> print_endline "duplicate ids"; None
            else ta
        | _ -> ta

let parse_attr name str =
    let attrid = intern_string name in
    let strid = intern_string str in
    (attrid, strid)

let rec parse_attrs attrlist =
    match attrlist with
    | [] -> []
    | (name, value) :: t ->
        let ta = parse_attrs t in
        match value with
        | Pxp_core_types.A.Value str -> 
            if name = "id" then ta else
            (parse_attr name str) :: ta
        | _ -> print_endline "warning: found a non-value attribute"; ta

let parse_widget name attrs =
    let id = parse_id attrs in
    let statics = parse_attrs attrs in
    Some {wgt_name = name; wgt_id = id; wgt_num = BinNums.Coq_xH; wgt_statics = statics}


let rec parse_node root =
    match root#node_type with
    | Pxp_document.T_element name ->
            let wn = intern_string name in
            let subnodes = parse_sub_nodes root#sub_nodes in
            begin match parse_widget wn root#attributes with
            | None -> None
            | Some wi ->
                Some (GraphicsHierarchy (wi, subnodes))
            end
    | _ -> None

and parse_sub_nodes nodes =
    match nodes with
    | hd :: tl ->
        let tn = parse_sub_nodes tl in
        if is_element hd then
            match parse_node hd with
            | Some nd -> ICons (nd, tn)
            | None -> tn
        else tn
    | _ -> INil

let parse_xml_from_file filename =
    let spec = Pxp_tree_parser.default_spec in
    let config = Pxp_types.default_config in
    let source = Pxp_types.from_file filename in
    let doc =
        try
            Some (Pxp_tree_parser.parse_wfdocument_entity config source spec)
        with
        | Pxp_types.Validation_error _
        | Pxp_types.WF_error _
        | Pxp_types.Namespace_error _
        | Pxp_types.Error _
        | Pxp_types.At(_,_) as error ->
            print_endline ("PXP error " ^ Pxp_types.string_of_exn error); None
    in
    doc

let parse_from_file fn = 
    match parse_xml_from_file fn with
    | None -> None
    | Some doc -> parse_node doc#root
