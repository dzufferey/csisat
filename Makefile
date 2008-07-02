RM = rm -rf
PWD = $(shell pwd)

INLCUDES = -I $(PWD)/glpk_ml_wrapper/include -I $(PWD)/pico_ml_wrapper/include
LIB_GLPK_DIR = /usr/local/lib

ifndef STATIC
GLPK = #/usr/lib/libglpk.a # Uncomment for GLPK < 4.28
LIBS = -cclib '-L $(PWD)/glpk_ml_wrapper/ -L $(PWD)/pico_ml_wrapper/ -L $(PWD)/picosat-632 -lglpk -lpicosat -lcamlpico -lcamlglpk'
else
GLPK = $(LIB_GLPK_DIR)/libglpk.a /usr/lib/libz.a /usr/lib/libltdl.a /usr/lib/libdl.a # for GLPK 4.28
LIBS = -ccopt '-static' -cclib '-L $(PWD)/glpk_ml_wrapper/ -L $(PWD)/pico_ml_wrapper/ -L $(PWD)/picosat-632 -lm -ldl -lltdl -lz -lglpk -lpicosat -lcamlpico -lcamlglpk'
endif

OCAML_OPT_C = $(shell if which ocamlopt.opt 2> /dev/null > /dev/null ; then echo ocamlopt.opt; else echo ocamlopt; fi)
OCAML_OPT_LEX = $(shell if which ocamllex.opt 2> /dev/null > /dev/null ; then echo ocamllex.opt; else echo ocamllex; fi)
OCAML_OPT_YACC = $(shell if which ocamlyacc.opt 2> /dev/null > /dev/null ; then echo ocamlyacc.opt; else echo ocamlyacc; fi)

COMPILE_FLAG = -inline 10
#COMPILE_FLAG = -p

OBJ = obj
SRC = src
DOC = doc

FILES = \
	$(OBJ)/message.cmx \
	$(OBJ)/ordSet.cmx \
	$(OBJ)/utils.cmx \
	$(OBJ)/ast.cmx \
	$(OBJ)/astUtil.cmx \
	$(OBJ)/dpllClause.cmx \
	$(OBJ)/dpllProof.cmx \
	$(OBJ)/satInterface.cmx \
	$(OBJ)/picoInterface.cmx \
	$(OBJ)/dpllCore.cmx \
	$(OBJ)/matrix.cmx \
	$(OBJ)/LIUtils.cmx \
	$(OBJ)/infixLex.cmx \
	$(OBJ)/infixParse.cmx \
	$(OBJ)/fociPrinter.cmx \
	$(OBJ)/fociLex.cmx \
	$(OBJ)/fociParse.cmx \
	$(OBJ)/clpLI.cmx \
	$(OBJ)/dag.cmx \
	$(OBJ)/satUIF.cmx \
	$(OBJ)/satLI.cmx \
	$(OBJ)/nelsonOppen.cmx \
	$(OBJ)/satPL.cmx \
	$(OBJ)/interpolate.cmx \
	$(OBJ)/config.cmx \
	$(OBJ)/tests.cmx \
	$(OBJ)/main.cmx

TARGET = bin/csisat


all: glpk pico picosat $(FILES)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -o $(TARGET) $(LIBS)  $(GLPK) $(PWD)/picosat-632/libpicosat.a $(FILES)
	$(shell sed -i 's/Version:.*\\n\\n/Version: REV, DATE\.\\n\\n/g' $(SRC)/config.ml)

VERSION = $(shell svn info | grep -i "revision" | cut -f 2 -d ' ')
DATE = $(shell date)

### Part for parsers and lexers ####

#FOCI-like syntax
$(OBJ)/fociParse.mli: $(OBJ)/fociParse.ml

$(OBJ)/fociParse.cmi: $(OBJ)/fociParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/fociLex.cmx: $(OBJ)/fociParse.cmi $(OBJ)/fociLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/fociLex.ml

#INFIX syntax
$(OBJ)/infixParse.mli: $(OBJ)/infixParse.ml

$(OBJ)/infixParse.cmi: $(OBJ)/infixParse.mli
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/infixLex.cmx: $(OBJ)/infixParse.cmi $(OBJ)/infixLex.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $(OBJ)/infixLex.ml

####################################

$(OBJ)/%.ml: $(SRC)/io/%.mll
	@mkdir -p $(OBJ)
	$(OCAML_OPT_LEX) -o $@ $< 

$(OBJ)/%.ml: $(SRC)/io/%.mly
	@mkdir -p $(OBJ)
	$(OCAML_OPT_YACC) $< 
	mv $(patsubst %.mly, %.ml, $<) $@
	mv $(patsubst %.mly, %.mli, $<) $(patsubst %.ml, %.mli, $@)


$(OBJ)/%.cmx: $(OBJ)/%.ml
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<

$(OBJ)/%.cmx: $(SRC)/%.ml
	@mkdir -p $(OBJ)
	$(shell if test $< = $(SRC)/config.ml; \
		then sed -i 's/Version: REV, DATE/Version: revision $(VERSION), $(DATE)/g' $<; fi)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	mv $(patsubst %.ml, %.cmx, $<) $@
	mv $(patsubst %.ml, %.cmi, $<) $(patsubst %.cmx, %.cmi, $@)
	mv $(patsubst %.ml, %.o, $<) $(patsubst %.cmx, %.o, $@)

.PHONY: doc

doc: odoc

odoc:
	$(shell if test -e $(DOC)/index.html ; then rm -rf $(DOC)/* ; fi)
	@mkdir -p $(DOC)
	ocamldoc \
		-v \
		-d $(DOC) \
		-I $(OBJ) $(INLCUDES) \
		-html \
		-stars \
		-hide Set.Make,Char \
		$(patsubst $(OBJ)/%, $(SRC)/%, $(patsubst %.cmx, %.ml, $(FILES)))

glpk:
	cd glpk_ml_wrapper; make

pico:
	cd pico_ml_wrapper; make

picosat:
	cd picosat-632; ./configure;  make

clean:
	$(RM) $(TARGET) $(OBJ)/*
	cd glpk_ml_wrapper; make clean
	cd pico_ml_wrapper; make clean
	cd picosat-632; make clean
