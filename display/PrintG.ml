open GTree
open Camlcoq
open Format

let rec print_ident p level =
    if level > 0 then 
    (fprintf p "\t"; print_ident p (level - 1))
    else ()

let rec print_node p level node =
    match node with 
    | GNode (id, subnodes, attrs) ->
        print_ident p level;
        fprintf p "%s(" (extern_atom id);
        print_attrs p attrs;
        fprintf p ")\n";
        print_nodes p (level + 1) subnodes

and print_nodes p level nodes =
    match nodes with
    | GNil -> ()
    | GCons (hdn, tln) -> 
        print_node p level hdn;
        print_nodes p level tln

and print_attrs p attrs =
    match attrs with
    | [] -> ()
    | hd :: tl -> print_attr p hd;
        List.iter (fun attr -> fprintf p ", " ; print_attr p attr) tl

and print_attr p attr =
    match attr with
    | SConst (id, (GString cosid)) ->
        fprintf p "%s: \"%s\"" (extern_atom id) (extern_atom cosid)
    | SNodeRef (id, nd, sl) ->
        fprintf p "%s: ref to %s.%s" (extern_atom id) (extern_atom nd) (extern_atom sl)
    | _ -> ()
