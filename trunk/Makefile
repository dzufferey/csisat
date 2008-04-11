RM = rm -rf
PWD = $(shell pwd)

INLCUDES = -I $(PWD)/glpk_ml_wrapper/include -I $(PWD)/pico_ml_wrapper/include
LIBS = -cclib '-L $(PWD)/glpk_ml_wrapper/ -L $(PWD)/pico_ml_wrapper/ -L $(PWD)/picosat-632 -lm -lglpk -lpicosat -lcamlpico -lcamlglpk'
GLPK = /usr/lib/libglpk.a
STATIC = 
#STATIC = -ccopt '-static'

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
	$(OBJ)/main.cmx

TARGET = bin/csisat


all: glpk pico picosat $(FILES)
	$(OCAML_OPT_C) $(COMPILE_FLAG) -o $(TARGET) $(STATIC) $(LIBS)  $(GLPK) $(PWD)/picosat-632/libpicosat.a $(FILES)

$(OBJ)/%.cmx: $(SRC)/%.ml
	@mkdir -p $(OBJ)
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
