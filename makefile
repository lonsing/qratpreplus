#CFLAGS=-Wextra -Wall -Wno-unused -std=gnu99 -g3
CFLAGS=-Wextra -Wall -Wno-unused -std=gnu99 -DNDEBUG -O3
#CFLAGS=-Wextra -Wall -Wno-unused -std=gnu99 -DNDEBUG -g3 -pg -fprofile-arcs -ftest-coverage -static

LFLAGS=

MAJOR=2
MINOR=0
VERSION=$(MAJOR).$(MINOR)

TARGETS:=qratpreplus_main.o libqratpreplus.a

UNAME:=$(shell uname)

ifeq ($(UNAME), Darwin)
# Mac OS X
SONAME=-install_name
TARGETS+=libqratpreplus.$(VERSION).dylib
else
SONAME=-soname
TARGETS+=libqratpreplus.so.$(VERSION)
endif

.SUFFIXES: .c .o .fpico

.c.fpico:
	$(CC) $(CFLAGS) -fPIC -c $< -o $@

.c.o:
	$(CC) $(CFLAGS) -c $< -o $@

qratpre+: $(TARGETS)
	$(CC) $(CFLAGS) qratpreplus_main.o -L. -lqratpreplus -o qratpre+

qratpreplus_main.o: qratpreplus_main.c qratpreplus.h

mem.o: mem.c mem.h
mem.fpico: mem.c mem.h 

parse.o: parse.c parse.h util.h qratpreplus_internals.h qratpreplus.h
parse.fpico: parse.c parse.h util.h qratpreplus_internals.h qratpreplus.h 

qbce_qrat_plus.o: qbce_qrat_plus.c qbce_qrat_plus.h qratpreplus.h stack.h qratpreplus_internals.h qbcp.h util.h
qbce_qrat_plus.fpico: qbce_qrat_plus.c qbce_qrat_plus.h qratpreplus.h stack.h qratpreplus_internals.h qbcp.h util.h

qbcp.o: qbcp.c qbcp.h util.h qratpreplus_internals.h
qbcp.fpico: qbcp.c qbcp.h util.h qratpreplus_internals.h 

qratpreplus.o: qratpreplus.c qratpreplus.h qratpreplus_internals.h qbce_qrat_plus.h parse.h util.h mem.h stack.h
qratpreplus.fpico: qratpreplus.c qratpreplus.h qratpreplus_internals.h qbce_qrat_plus.h parse.h util.h mem.h stack.h

qratpreplus_main.o: qratpreplus_main.c qratpreplus.h
qratpreplus_main.fpico: qratpreplus_main.c qratpreplus.h

util.o: util.c util.h qratpreplus_internals.h
util.fpico: util.c util.h qratpreplus_internals.h

#################


libqratpreplus.a: qratpreplus.o qbce_qrat_plus.o parse.o util.o mem.o qbcp.o  
	ar rc $@ $^
	ranlib $@

libqratpreplus.so.$(VERSION): qratpreplus.fpico qbce_qrat_plus.fpico parse.fpico util.fpico mem.fpico qbcp.fpico 
	$(CC) $(LFLAGS) -shared -Wl,$(SONAME),libqratpreplus.so.$(MAJOR) $^ -o $@

libqratpreplus.$(VERSION).dylib: qratpreplus.fpico qbce_qrat_plus.fpico parse.fpico util.fpico mem.fpico qbcp.fpico
	$(CC) $(LFLAGS) -shared -Wl,$(SONAME),libqratpreplus.$(MAJOR).dylib $^ -o $@

clean:
	rm -f *.so.$(VERSION) *.dylib *.fpico *.a *.o *.gcno *.gcda *.gcov *~ gmon.out qratpre+
