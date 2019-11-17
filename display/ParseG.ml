open Camlcoq
open GTree

let is_element node =
    match node#node_type with
    | Pxp_document.T_element _ -> true
    | _ -> false

let rec parse_node root =
    match root#node_type with
    | Pxp_document.T_element name ->
            let id = intern_string name in
            let subnodes = parse_sub_nodes root#sub_nodes in
            let attrs = parse_attrs root#attributes in
            Some (GNode (id, subnodes, attrs))
    | _ -> None

and parse_sub_nodes nodes =
    match nodes with
    | hd :: tl ->
        let tn = parse_sub_nodes tl in
        if is_element hd then
            match parse_node hd with
            | Some nd -> GCons (nd, tn)
            | None -> tn
        else tn
    | _ -> GNil

and parse_attrs attrlist =
    match attrlist with
    | [] -> []
    | (name, value) :: t ->
        let ta = parse_attrs t in
        match value with
        | Pxp_core_types.A.Value str -> (parse_attr name str) :: ta
        | _ -> ta

and parse_attr name str =
    let ref_reg = Str.regexp "@\\([_a-zA-Z][_a-zA-Z0-9]+\\)\\.\\([_a-zA-Z][_a-zA-Z0-9]+\\)" in
    let attrid = intern_string name in
    if Str.string_match ref_reg str 0 then
        (*node reference *)
        let nd = Str.matched_group 1 str in
        let pa = Str.matched_group 2 str in
        SNodeRef (attrid, (intern_string nd), (intern_string pa))
    else
        (*const*)
        let strid = intern_string str in
        SConst (attrid, (GString strid))

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
            print_endline ("PXP error " ^ Pxp_types.string_of_exn error);None
    in
    doc

let parse_from_file filename = 
    match parse_xml_from_file filename with
    | None -> None
    | Some doc -> parse_node doc#root
