COM = ocamlc -I ../extraction
LEX = ocamllex
YACC = ocamlyacc

all : ocaml_lexer.ml ocaml_parser.ml display_lexer.ml display_parser.ml
	rm -rf *.mli *.cmi *.cmo ../extraction/*.cmi
	mv ocaml_lexer.ml ../extraction
	mv ocaml_parser.ml ../extraction
	mv display_lexer.ml ../extraction
	mv display_parser.ml ../extraction

ocaml_lexer.ml : ocaml_lexer.mll
	$(LEX) $<

ocaml_parser.ml ocaml_parser.mli : ocaml_parser.mly
	$(YACC) $<

display_lexer.ml : display_lexer.mll
	$(LEX) $<

display_parser.ml display_parser.mli : display_parser.mly
	$(YACC) $<

.PHONY clean :
	rm -rf ../extraction/*.cmi *.cmi *.cmo *.mli ocaml_parser.ml ocaml_lexer.ml display_parser.ml display_lexer.ml
