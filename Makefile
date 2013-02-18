.PHONY: clean distclean pack count

# OS type: Linux/Win DJGPP
ifdef OS
   EXE=.exe
else
   EXE=
endif

EXEFILE=llamac$(EXE)
MLFILES=Types.ml Udt.ml Hashcons.ml Identifier.ml \
   Error.ml Symbol.ml Quads.ml Ast.ml TypeInference.ml Debug.ml \
   TypeChecker.ml Icode.ml \
   Scanner.ml Parser.ml Main.ml
MLIFILES=Types.mli Udt.mli Hashcons.mli Identifier.mli \
   Error.mli Symbol.mli Quads.mli Ast.mli TypeInference.mli Debug.mli \
   TypeChecker.mli Icode.mli \
   Parser.mli Scanner.mli
CMOFILES=$(patsubst %.ml,%.cmo,$(MLFILES))
CMIFILES=$(patsubst %.ml,%.cmi,$(MLFILES))
CMXFILES=$(patsubst %.ml,%.cmx,$(MLFILES))
OBJFILES=$(patsubst %.ml,%.o,$(MLFILES))
PARSERFILES=Parser.ml Parser.mli Parser.output Scanner.ml
SRCFILES=Makefile extend.ml Scanner.mll Parser.mly \
  $(filter-out Parser.% Scanner.%,$(MLFILES)) \
  $(filter-out Parser.%,$(MLIFILES))

CAMLP5_FLAGS=-pp "camlp5o ./extend.cmo"
OCAMLC_FLAGS=-g -I +ocamlgraph
OCAMLOPT_FLAGS=
OCAMLC=ocamlc $(OCAMLC_FLAGS)
OCAMLOPT=ocamlopt $(OCAMLOPT_FLAGS)
OCAMLDEP=ocamldep
INCLUDES=

default: llamac$(EXE)

all: $(EXEFILE)

extend.cmo: extend.ml
	$(OCAMLC) -pp "camlp5o pa_extend.cmo q_MLast.cmo" -I +camlp5 -c $<

%.cmo: %.ml %.mli extend.cmo
	$(OCAMLC) $(CAMLP5_FLAGS) -c $<

%.cmx: %.ml extend.cmo
	$(OCAMLOPT) $(CAMLP5_FLAGS) -c $<

%.cmi: %.mli extend.cmo
	$(OCAMLC) $(CAMLP5_FLAGS) -c $<

%.cmo %.cmi: %.ml extend.cmo
	$(OCAMLC) $(CAMLP5_FLAGS) -c $<

.PHONY: all clean count depend

$(EXEFILE): Parser.mli Scanner.ml $(CMOFILES)
	$(OCAMLC) -o $@ $(CMOFILES)

Parser.ml Parser.mli: Parser.mly
	ocamlyacc -v Parser.mly

Scanner.ml: Scanner.mll
	ocamllex Scanner.mll

-include .depend

depend: $(MLFILES) $(MLIFILES) extend.cmo
	$(OCAMLDEP) $(CAMLP5_FLAGS) $(INCLUDES) \
          $(filter-out extend.cmo,$^) > .depend

clean:
	$(RM) $(CMXFILES) $(CMOFILES) $(CMIFILES) $(OBJFILES) $(EXEFILES) \
           extend.cmi extend.cmo \
           $(patsubst %,%.cm?,$(EXEFILES)) $(PARSERFILES) pplib.cma *~

distclean: clean
	$(RM) $(EXEFILE) llamac$(EXE) .depend

pack: clean
	tar cvfz llamac.tar.gz $(SRCFILES)

count:
	wc -l $(SRCFILES)
