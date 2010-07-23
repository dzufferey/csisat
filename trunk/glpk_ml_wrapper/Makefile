CC=gcc
CFLAGS= -O2 -Wall -fPIC
INCLUDE= 
LIBS= -lglpk

SRC = src/camlglpk.c
OBJ = src/camlglpk.o

TARGET= libcamlglpk.a

all:
	@echo compiling interface
	cd include; ocamlc -c camlglpk.mli
	@echo compiling $(TARGET)
	$(CC) -c $(INCLUDE) $(SRC) $(CFLAGS) -o $(OBJ)
	ar rc $(TARGET) $(OBJ)
	ranlib $(TARGET)

clean:
	rm -r include/camlglpk.cmi $(TARGET) $(OBJ)
	@echo cleaned.

distclean:	clean
