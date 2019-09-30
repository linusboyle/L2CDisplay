open Parse
open PrintDisplay

(*simple driver*)
let () = 
    let parsed = parse_display_from_file "test.xml" in
    match parsed with
    | None -> print_endline "Parsing error"
    | Some display ->
        print_display display
