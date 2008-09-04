RM = rm -rf
PWD = $(shell pwd)

OBJ = obj
SRC = src
DOC = doc
LIB = lib

INLCUDES = -I $(PWD)/glpk_ml_wrapper/include -I $(PWD)/pico_ml_wrapper/include
LIB_GLPK_DIR = /usr/lib

ifndef STATIC
GLPK = #/usr/lib/libglpk.a # Uncomment for GLPK < 4.28
LIBS = -cclib '-L $(PWD)/$(LIB) \
	-lglpk -lpicosat -lcamlpico -lcamlglpk'
else
GLPK = $(LIB_GLPK_DIR)/libglpk.a  /usr/lib/libgmp.a /usr/lib/libz.a /usr/lib/libltdl.a /usr/lib/libdl.a # for GLPK 4.28
LIBS = -ccopt '-static' \
	-cclib '-L $(PWD)/$(LIB) \
	-lm -ldl -lltdl -lz -lglpk -lpicosat -lcamlpico -lcamlglpk'
endif

OCAML_C = $(shell if which ocamlc.opt 2> /dev/null > /dev/null ; then echo ocamlc.opt; else echo ocamlc; fi)
OCAML_LD = $(OCAML_C)
OCAML_OPT_C = $(shell if which ocamlopt.opt 2> /dev/null > /dev/null ; then echo ocamlopt.opt; else echo ocamlopt; fi)
OCAML_OPT_LD = $(OCAML_OPT_C)
OCAML_OPT_LEX = $(shell if which ocamllex.opt 2> /dev/null > /dev/null ; then echo ocamllex.opt; else echo ocamllex; fi)
OCAML_OPT_YACC = $(shell if which ocamlyacc.opt 2> /dev/null > /dev/null ; then echo ocamlyacc.opt; else echo ocamlyacc; fi)

COMPILE_FLAG = -inline 10
#COMPILE_FLAG = -p
OCAML_LD_FLAGS = 


FILES = \
	$(OBJ)/csisatMessage.cmx \
	$(OBJ)/csisatOrdSet.cmx \
	$(OBJ)/csisatUtils.cmx \
	$(OBJ)/csisatAst.cmx \
	$(OBJ)/csisatAstUtil.cmx \
	$(OBJ)/csisatDpllClause.cmx \
	$(OBJ)/csisatDpllProof.cmx \
	$(OBJ)/csisatSatInterface.cmx \
	$(OBJ)/csisatPicoInterface.cmx \
	$(OBJ)/csisatDpllCore.cmx \
	$(OBJ)/csisatMatrix.cmx \
	$(OBJ)/csisatLIUtils.cmx \
	$(OBJ)/csisatInfixLex.cmx \
	$(OBJ)/csisatInfixParse.cmx \
	$(OBJ)/csisatFociPrinter.cmx \
	$(OBJ)/csisatFociLex.cmx \
	$(OBJ)/csisatFociParse.cmx \
	$(OBJ)/csisatDimacsLex.cmx \
	$(OBJ)/csisatDimacsParse.cmx \
	$(OBJ)/csisatClpLI.cmx \
	$(OBJ)/csisatDag.cmx \
	$(OBJ)/csisatSatUIF.cmx \
	$(OBJ)/csisatSatLI.cmx \
	$(OBJ)/csisatNelsonOppen.cmx \
	$(OBJ)/csisatSatPL.cmx \
	$(OBJ)/csisatInterpolate.cmx \
	$(OBJ)/csisatConfig.cmx \
	$(OBJ)/csisatTests.cmx

MAIN =  $(OBJ)/csisatMain.cmx
TARGET = bin/csisat
OCAML_LIB = libcsisat


all: glpk pico picosat server $(FILES) $(MAIN) lib
	$(OCAML_OPT_C) $(COMPILE_FLAG) -o $(TARGET) $(LIBS)  $(GLPK) $(PWD)/picosat-632/libpicosat.a $(FILES) $(MAIN)
	$(shell sed -i 's/Version .*\\n\\n/Version 1.2 (Rev REV, Build DATE)\.\\n\\n/g' $(SRC)/csisatConfig.ml)

VERSION = $(shell svnversion)
DATE = $(shell date -u +%Y-%m-%dT%H:%M:%S)

### Part for parsers and lexers ####

#FOCI-like syntax
$(OBJ)/csisatFociParse.mli: $(OBJ)/csisatFociParse.ml

$(OBJ)/csisatFociParse.cmi: $(OBJ)/csisatFociParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/csisatFociLex.cmx: $(OBJ)/csisatFociParse.cmi $(OBJ)/csisatFociLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatFociLex.ml
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatFociLex.ml

#INFIX syntax
$(OBJ)/csisatInfixParse.mli: $(OBJ)/csisatInfixParse.ml

$(OBJ)/csisatInfixParse.cmi: $(OBJ)/csisatInfixParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/csisatInfixLex.cmx: $(OBJ)/csisatInfixParse.cmi $(OBJ)/csisatInfixLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatInfixLex.ml
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatInfixLex.ml

#DIMACS syntax
$(OBJ)/csisatDimacsParse.mli: $(OBJ)/csisatDimacsParse.ml

$(OBJ)/csisatDimacsParse.cmi: $(OBJ)/csisatDimacsParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/csisatDimacsLex.cmx: $(OBJ)/csisatDimacsParse.cmi $(OBJ)/csisatDimacsLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatDimacsLex.ml
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $(OBJ)/csisatDimacsLex.ml

####################################

$(OBJ)/%.ml: $(SRC)/io/%.mll
	@mkdir -p $(OBJ)
	$(OCAML_OPT_LEX) -o $@ $< 

$(OBJ)/%.ml: $(SRC)/io/%.mly
	@mkdir -p $(OBJ)
	$(OCAML_OPT_YACC) $< 
	@mv $(patsubst %.mly, %.ml, $<) $@
	@mv $(patsubst %.mly, %.mli, $<) $(patsubst %.ml, %.mli, $@)


$(OBJ)/%.cmx: $(OBJ)/%.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/%.cmx: $(SRC)/%.ml
	@mkdir -p $(OBJ)
	$(shell if test $< = $(SRC)/csisatConfig.ml; \
		then sed -i 's/Rev REV, Build DATE/Rev $(VERSION), Build $(DATE)/g' $<; fi)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	$(OCAML_C) -I $(OBJ) $(INLCUDES) -c $<
	@mv $(patsubst %.ml, %.cmx, $<) $@
	@mv $(patsubst %.ml, %.cmi, $<) $(patsubst %.cmx, %.cmi, $@)
	@mv $(patsubst %.ml, %.cmo, $<) $(patsubst %.cmx, %.cmo, $@)
	@mv $(patsubst %.ml, %.o, $<) $(patsubst %.cmx, %.o, $@)

lib: $(LIB)/$(OCAML_LIB).cma $(LIB)/$(OCAML_LIB).cmxa 

$(LIB)/$(OCAML_LIB).cma: $(OCAML_LIB_OBJ:%=%.cmo)
	@echo Creating OCAML \(byte code\) library $@
	@mkdir -p $(LIB)
	$(OCAML_LD) $(OCAML_LD_FLAGS) -a -o $@ $(patsubst %.cmx, %.cmo, $(FILES))

$(LIB)/$(OCAML_LIB).cmxa $(LIB)/$(OCAML_LIB).a: $(OCAML_LIB_OBJ:%=%.cmx)
	@echo Creating OCAML \(native code\) library $@
	@mkdir -p $(LIB)
	$(OCAML_OPT_LD) $(OCAML_LD_FLAGS) -a -o $@ $(FILES)

.PHONY: doc server

doc: odoc

HIDE = Set.Make,Char

odoc:
	$(shell if test -e $(DOC)/index.html ; then rm -rf $(DOC)/* ; fi)
	@mkdir -p $(DOC)
	ocamldoc \
		-v \
		-d $(DOC) \
		-I $(OBJ) $(INLCUDES) \
		-html \
		-stars \
		-hide $(HIDE) \
		$(patsubst $(OBJ)/%, $(SRC)/%, $(patsubst %.cmx, %.ml, $(FILES)))

glpk:
	cd glpk_ml_wrapper; make
	@mkdir -p $(LIB)
	cp glpk_ml_wrapper/libcamlglpk.a $(LIB)/

pico:
	cd pico_ml_wrapper; make
	@mkdir -p $(LIB)
	cp pico_ml_wrapper/libcamlpico.a $(LIB)/

picosat:
	cd picosat-632; ./configure;  make
	@mkdir -p $(LIB)
	cp picosat-632/libpicosat.a $(LIB)/

server:
	cd server; make

clean:
	$(RM) $(TARGET) $(OBJ)/* $(LIB)/*
	cd glpk_ml_wrapper; make clean
	cd pico_ml_wrapper; make clean
	cd picosat-632; make clean
	cd server; make clean
