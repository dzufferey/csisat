CC=gcc
CFLAGS= -O2 -Wall -fPIC
INCLUDE= -I../picosat
LIBS= -lpicosat -L../picosat
RM = /bin/rm -f

SRC = src/camlpico.c
OBJ = src/camlpico.o

TARGET= libcamlpico.a

all:
	@echo compiling interface
	cd include; ocamlc -c camlpico.mli
	@echo compiling $(TARGET)
	$(CC) -c $(INCLUDE) $(SRC) $(CFLAGS) -o $(OBJ)
	ar rc $(TARGET) $(OBJ)
	ranlib $(TARGET)

clean:
	$(RM) $(TARGET) $(OBJ) include/camlpico.cmi 
	@echo cleaned.

distclean:	clean
