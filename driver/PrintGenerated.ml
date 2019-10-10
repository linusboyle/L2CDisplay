open ParseDisplay
open PrintClight
open DisplayClightGen
open Format

let () = 
    let parsed = parse_display_from_file "test.xml" in
    match parsed with
    | None -> print_endline "Parsing error"
    | Some display ->
    let program = trans_program display in
    print_program std_formatter program
