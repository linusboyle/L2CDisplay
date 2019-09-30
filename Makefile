FLOCQDIR=compcert/flocq

DIRS=compcert/lib compcert/common compcert/ia32 compcert src extraction frontend $(FLOCQDIR)/Core $(FLOCQDIR)/Prop $(FLOCQDIR)/Calc $(FLOCQDIR)/Appli

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

TARGET=Test.native

# Flocq
FLOCQ_CORE=Fcore_float_prop.v Fcore_Zaux.v Fcore_rnd_ne.v Fcore_FTZ.v \
  Fcore_FLT.v Fcore_defs.v Fcore_Raux.v Fcore_ulp.v Fcore_rnd.v Fcore_FLX.v \
  Fcore_FIX.v Fcore_digits.v Fcore_generic_fmt.v Fcore.v
FLOCQ_PROP=Fprop_Sterbenz.v Fprop_mult_error.v Fprop_relative.v \
  Fprop_div_sqrt_error.v Fprop_plus_error.v
FLOCQ_CALC=Fcalc_ops.v Fcalc_bracket.v Fcalc_sqrt.v Fcalc_div.v Fcalc_round.v \
  Fcalc_digits.v
FLOCQ_APPLI=Fappli_rnd_odd.v Fappli_IEEE_bits.v Fappli_IEEE.v
FLOCQ=$(FLOCQ_CORE) $(FLOCQ_PROP) $(FLOCQ_CALC) $(FLOCQ_APPLI)

LIB=Axioms.v Coqlib.v Intv.v Maps.v Heaps.v Lattice.v Ordered.v \
  Iteration.v Integers.v Floats.v Parmov.v UnionFind.v Wfsimpl.v Fappli_IEEE_extra.v

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v Values.v \
  Smallstep.v Behaviors.v Switch.v Determinism.v

ARCH=Archi.v

SEMANTICS=ClightBigstep.v

COMPCERT=$(LIB) $(COMMON) $(ARCH) $(FLOCQ) Ctypes.v Cop.v Clight.v

FILES=Display.v ClightGen.v $(COMPCERT)

.PHONY: proof extraction compile coqide

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
	$(OCAMLBUILD) $(OCB_OPTIONS) $(TARGET)

coqide:
	coqide $(INCLUDES)
