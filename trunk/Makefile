RM = rm -rf
PWD = $(shell pwd)

INLCUDES = -I $(PWD)/glpk_ml_wrapper/include -I $(PWD)/pico_ml_wrapper/include
LIB_GLPK_DIR = /usr/local/lib

ifndef STATIC
#GLPK = /usr/lib/libglpk.a # Uncomment for GLPK < 4.28
LIBS = -cclib '-L $(PWD)/glpk_ml_wrapper/ -L $(PWD)/pico_ml_wrapper/ -L $(PWD)/picosat-632 -lglpk -lpicosat -lcamlpico -lcamlglpk'
else
GLPK = $(LIB_GLPK_DIR)/libglpk.a /usr/lib/libz.a /usr/lib/libltdl.a /usr/lib/libdl.a # for GLPK 4.28
LIBS = -ccopt '-static' -cclib '-L $(PWD)/glpk_ml_wrapper/ -L $(PWD)/pico_ml_wrapper/ -L $(PWD)/picosat-632 -lm -ldl -lltdl -lz -lglpk -lpicosat -lcamlpico -lcamlglpk'
endif

OCAML_OPT_C = $(shell if which ocamlopt.opt 2> /dev/null > /dev/null ; then echo ocamlopt.opt; else echo ocamlopt; fi)

COMPILE_FLAG = -inline 10
#COMPILE_FLAG = -p

OBJ = obj
SRC = src

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
	$(OBJ)/fociPrinter.cmx \
	$(OBJ)/fociParser.cmx \
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

$(OBJ)/%.cmx: $(SRC)/%.ml
	@mkdir -p $(OBJ)
	$(shell if test $< = $(SRC)/config.ml; \
		then sed -i 's/Version: REV, DATE/Version: revision $(VERSION), $(DATE)/g' $<; fi)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -I $(OBJ) $(INLCUDES) -c $<
	mv $(patsubst %.ml, %.cmx, $<) $@
	mv $(patsubst %.ml, %.cmi, $<) $(patsubst %.cmx, %.cmi, $@)
	mv $(patsubst %.ml, %.o, $<) $(patsubst %.cmx, %.o, $@)


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
