CC=gcc
CFLAGS= -O2 -Wall
LIBS= -lpthread
RM = /bin/rm -f

SRC = csisatServer.c

TARGET= ../bin/csisatServer

all:
	@echo compiling csisatServer
	gcc $(CFLAGS) $(SRC) $(LIBS) -o $(TARGET)

clean:
	$(RM) $(TARGET)
	@echo cleaned.

distclean:	clean
