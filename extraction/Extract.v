Require Import ExtrOcamlBasic.
Require Import ExtrOcamlString.
Require Import Floats.
Require Import ClightGen.

Cd "extraction".

Extraction Blacklist List String.
Extract Constant ClightGen.intern_string =>
  "(fun s -> Camlcoq.intern_string (Util.camlstring_of_coqstring s))".
Separate Extraction trans_program Floats.
