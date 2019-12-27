Require AST.
Require Floats.
Require String.
Require Maps.
Require LDisplay.
Require TransType.
Require Compiler.
Require Errors.
Require DisplayWGen.
Require LustreWGenDis.
Require ControlGen.
Require ClightGenDis.

Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.

(* AST *)
Extract Constant AST.ident_of_string =>
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".

(* Avoid name clashes *)
Extraction Blacklist List String Int.

(* Compiler *)
Extract Constant Compiler.print_LustreT => "PrintLustreS.print_LustreT".
Extract Constant Compiler.print_LustreS => "PrintLustreS.print_LustreS".
Extract Constant Compiler.print_LustreR1 => "PrintLustreR.print_LustreR1".
Extract Constant Compiler.print_LustreR2 => "PrintLustreR.print_LustreR2".
Extract Constant Compiler.print_LustreR3 => "PrintLustreR.print_LustreR3".
Extract Constant Compiler.print_LustreF1 => "PrintLustreF.print_LustreF1".
Extract Constant Compiler.print_LustreF2 => "PrintLustreF.print_LustreF2".
Extract Constant Compiler.print_LustreE1 => "PrintLustreF.print_LustreE1".
Extract Constant Compiler.print_LustreE2 => "PrintLustreF.print_LustreE2".
Extract Constant Compiler.print_LustreD => "PrintLustreF.print_LustreD".
Extract Constant Compiler.print_LustreC => "PrintLustreF.print_LustreC".
Extract Constant Compiler.print_Ctemp => "PrintCtemp.print_if".
Extract Constant Compiler.print => "fun (f: 'a -> unit) (x: 'a) -> f x; x".

(* Cutting the dependancy to R. *)
Extract Inlined Constant Fcore_defs.F2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.FF2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.B2R => "fun _ -> assert false".
Extract Inlined Constant Fappli_IEEE.round_mode => "fun _ -> assert false".
Extract Inlined Constant Fcalc_bracket.inbetween_loc => "fun _ -> assert false".

Extract Constant Lident.string_of_positive => 
  "fun i -> Camlcoq.coqstring_of_camlstring(string_of_int (Int32.to_int (Camlcoq.P.to_int32 i)))".
Extract Constant Lident.intern_string => 
  "fun s -> Camlcoq.intern_string (Camlcoq.camlstring_of_coqstring s)".
Extract Constant Lident.extern_atom => 
  "fun id -> Camlcoq.coqstring_of_camlstring (Camlcoq.extern_atom id)".

Cd "extraction".


Extract Constant LDisplay.str => "string".

Extract Constant TransType.nullstr => """""".

Extract Constant DisplayWGen.zero => """0""".
Extract Constant DisplayWGen.bool_of_str => 
  "fun s -> bool_of_string s".
Extract Constant DisplayWGen.int_of_str => 
  "fun s -> Camlcoq.coqint_of_camlint(Int32.of_string s)".
Extract Constant DisplayWGen.real_of_str => 
  "fun s -> Camlcoq.coqfloat_of_camlfloat(float_of_string s)".

Extract Constant ControlGen.int_of_str => 
  "fun s -> Camlcoq.coqint_of_camlint(Int32.of_string (Camlcoq.camlstring_of_coqstring s))".
Extract Constant ControlGen.real_of_str => 
  "fun s -> Camlcoq.coqfloat_of_camlfloat(float_of_string (Camlcoq.camlstring_of_coqstring s))".

Separate Extraction
  Compiler.transf_lt_program LustreSGen.trans_program
  LustreVGen.trans_program LustreWGenDis.trans_program 
  TransType.trans_program DisplayWGen.trans_program
  ControlGen.trans_control ClightGenDis.trans_program.
