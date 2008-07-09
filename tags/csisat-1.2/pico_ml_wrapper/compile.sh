#!/bin/sh
CFLAGS="-O2 -Wall"
INCLUDE="-ccopt -I../picosat-632 -ccopt -L../picosat-632 -ccopt -L. -I include"
LIBS="-cclib -lpicosat -cclib -lcamlpico"

echo ocamlopt $INCLUDE $LIBS ../picosat-632/libpicosat.a libcamlpico.a camlpico.mli test.ml  -o picoTest
ocamlopt $INCLUDE $LIBS ../picosat-632/libpicosat.a libcamlpico.a include/camlpico.mli test.ml  -o picoTest
