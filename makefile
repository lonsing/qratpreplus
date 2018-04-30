#CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -g3
CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -O3
#CFLAGS=-Wextra -Wall -Wno-unused -pedantic -std=c99 -DNDEBUG -g3 -pg -fprofile-arcs -ftest-coverage -static

qratpre+: mem.c stack.h qbce-qrat-plus.c qbce-qrat-plus.h qratplus.h qratplus.c qbcp.c qbcp.h
	$(CC) $(CFLAGS) qratplus.c mem.c qbce-qrat-plus.c qbcp.c -o qratpre+ 

clean:
	rm -f *.gcno *.gcda *.gcov *~ gmon.out qratpre+
