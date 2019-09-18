DIRS=src extraction frontend

VPATH=$(DIRS)
GPATH=$(DIRS)

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=coqc -q $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(INCLUDES)

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -use-ocamlfind \
  -j 2 \
  -pkg pxp \
  $(INCLUDES)

FILES=Display.v

.PHONY: proof extraction compile

all: depend proof extraction compile

proof: $(FILES:.v=.vo)

.SUFFIXES: .v .vo

.v.vo:
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

depend: $(FILES)
	@$(COQDEP) $^ > .depend

-include .depend

extraction:
	rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/Extract.v

compile: 
	$(OCAMLBUILD) $(OCB_OPTIONS) Test.native
