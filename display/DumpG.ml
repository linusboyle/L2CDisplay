open PrintG
open ParseG
open Format

let () =
    match parse_from_file "test2.xml" with
    | None -> print_endline "parsing error"
    | Some node -> print_node std_formatter 0 node
