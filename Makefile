FLOCQDIR=compcert/flocq

DIRS=compcert compcert/lib compcert/common compcert/ia32 display src driver frontend util \
	 $(FLOCQDIR)/Core $(FLOCQDIR)/Prop $(FLOCQDIR)/Calc $(FLOCQDIR)/Appli \
	 parser parser/validator

INCLUDES=$(patsubst %,-I %, $(DIRS))

COQC=coqc -q $(INCLUDES)
COQDEP=coqdep $(INCLUDES)
COQDOC=coqdoc
COQEXEC=coqtop $(INCLUDES) -batch -load-vernac-source
COQCHK=coqchk $(INCLUDES)
MENHIR=menhir

OCAMLBUILD=ocamlbuild
OCB_OPTIONS=\
  -use-ocamlfind \
  -j 2 			 \
  -I extraction  \
  -pkg pxp 		 \
  $(INCLUDES)

VPATH=$(DIRS)
GPATH=$(DIRS)

TARGET=Driver.native

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

LIB=Axioms.v Coqlib.v Intv.v Maps.v Integers.v Floats.v Fappli_IEEE_extra.v

COMMON=Errors.v AST.v Events.v Globalenvs.v Memdata.v Memtype.v Memory.v Values.v Smallstep.v

ARCH=Archi.v

SEMANTICS=ClightBigstep.v Lint.v Lvalues.v Lenv.v Lglobalenv.v Lsem.v LsemT.v LsemS.v LsemR.v LsemF.v LsemE.v LsemD.v LsemC.v

PROOFS=ExtraList.v Lenvmatch.v MemProof.v LsemTDeterm.v

LV2LS=LustreVGen.v LustreSGen.v SimplConstblock.v SimplConstblockProof.v

TOPOSORT=Toposort.v ToposortNodesProof.v ToposortStmtsProof.v Lu2ltProof.v

LS2LR=SimplLustreS.v LustreRGen.v TransTypecmp.v TransMainArgs.v Lt2lsProof.v SimplLustreSProof.v LustreRGenProof.v TransTypecmpProof.v TransMainArgsProof.v

LR2F=LustreFGen.v OutstructGen.v ClassifyRetsVar.v ResetfuncGen.v SimplEnv.v ClassifyArgsVar.v LustreFGenProof.v OutstructGenProof.v ClassifyRetsVarProof.v ResetfuncGenProof.v SimplEnvProof.v ClassifyArgsVarProof.v

LF2C=CtempGen.v ClightGen.v  CtempProof.v CtempGenProof.v Csem.v ClightGenProof.v

LUSTRE2C=Lident.v Ltypes.v Lop.v Lustre.v LustreV.v LustreW.v LustreS.v LustreR.v LustreF.v \
  Cltypes.v Clop.v Ctemp.v Ctypes.v Cop.v Clight.v $(SEMANTICS) $(PROOFS) $(LV2LS) $(TOPOSORT) $(LS2LR) $(LR2F) $(LF2C)

PARSERVALID= Alphabet.v Tuples.v Grammar.v Automaton.v Validator_safe.v Validator_complete.v \
  Interpreter.v Interpreter_correct.v Interpreter_complete.v Interpreter_safe.v Main.v

DRIVER=Tree.v TransTypeName.v LustreWGen.v Compiler.v

DISPLAY=DisplayClightGen.v GTree.v DisplayT.v DisplayTGen.v StructGen.v DisplayS.v DisplaySGen.v UpdateGen.v

PARSER=Parser.v Tokenizer.v

GENERATED=parser/Parser.v

FILES=$(LIB) $(COMMON) $(ARCH) $(LUSTRE2C) $(PARSERVALID) $(DRIVER) $(FLOCQ) $(DISPLAY) $(PARSER)

.PHONY: depend proof extraction parser test coqide

all: 
	@rm -f Version.ml
	@test -f .depend || $(MAKE) depend
	$(MAKE) proof
	$(MAKE) extraction
	$(MAKE) parser
	$(MAKE) compile

documentation: doc/coq2html $(FILES)
	mkdir -p doc/html
	rm -f doc/html/*.html
	doc/coq2html -o 'doc/html/%.html' doc/*.glob \
          $(filter-out doc/coq2html parser/Parser.v, $^)
	cp doc/coq2html.css doc/coq2html.js doc/html/

doc/coq2html: doc/coq2html.ml
	ocamlopt -w +a-29 -o doc/coq2html str.cmxa doc/coq2html.ml

doc/coq2html.ml: doc/coq2html.mll
	ocamllex -q doc/coq2html.mll

depend: $(GENERATED) depend1

depend1: $(FILES)
	@echo "Analyzing Coq Dependencies.."
	@$(COQDEP) $^ > .depend

proof: $(FILES:.v=.vo)

%.vo: %.v
	@rm -f doc/$(*F).glob
	@echo "COQC $*.v"
	@$(COQC) -dump-glob doc/$(*F).glob $*.v

parser/Parser.v : parser/Parser.vy
	@rm -f $@
	$(MENHIR) --coq parser/Parser.vy
	@chmod a-w $@

-include .depend

parser:
	$(MAKE) -C frontend
	ocamllex parser/Lexer.mll
	mv parser/Lexer.ml extraction

extraction: extraction/STAMP

extraction/STAMP: $(FILES:.v=.vo) extraction/Extract.v
	@rm -f extraction/*.ml extraction/*.mli
	$(COQEXEC) extraction/Extract.v
	@touch extraction/STAMP

compile: Version.ml
	$(OCAMLBUILD) $(OCB_OPTIONS) $(TARGET)

Version.ml:
	@echo "let version_msg=\"\\" >$@
	@echo "l2c : Lustre to C semantics preserving compiler." >>$@
	@echo "http://soft.cs.tsinghua.edu.cn/svn/l2c" >>$@
	@echo "Built on: `date +'%Y%m%d %H:%M:%S %z'`" >>$@
	@echo "Built by: `id -un`@`hostname`" >>$@
	@echo "" >>$@
	@echo "\";;" >>$@
	@echo "" >>$@

coqide:
	coqide $(INCLUDES)

test:
	$(OCAMLBUILD) $(OCB_OPTIONS) DumpG.native
