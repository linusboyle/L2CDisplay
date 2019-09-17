open Parse
open Display
open Util

(*simple driver*)
let spec = Pxp_tree_parser.default_spec
let config = Pxp_types.default_config
let source = Pxp_types.from_file "test.xml"

let () = 
    let doc = 
        try
            Pxp_tree_parser.parse_wfdocument_entity config source spec 
        with
        | Pxp_types.Validation_error _
        | Pxp_types.WF_error _
        | Pxp_types.Namespace_error _
        | Pxp_types.Error _
        | Pxp_types.At(_,_) as error ->
            print_endline ("PXP error " ^ Pxp_types.string_of_exn error);exit 1
    in
    let parsed = toXml doc#root in
    let rec print_xml xml =
        match xml with
        | XData data ->
                print_endline "data";
                print_endline (camlstring_of_coqstring data)
        | XElement (name, attrs, sub) -> 
                print_endline "element";
                print_endline (camlstring_of_coqstring name);
                print_attr attrs;
                List.iter print_xml sub
    and print_attr attrs =
        List.iter ( fun attr -> match attr with
                                | XAttr (name, value) ->
                                    print_endline "attribute";
                                    print_endline (camlstring_of_coqstring name);
                                    print_endline (camlstring_of_coqstring value))
        attrs
    in
    print_xml parsed
