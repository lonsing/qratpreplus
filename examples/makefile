SRCDIR = .
SRCFILES = $(wildcard $(SRCDIR)/*.c)
OBJS = $(patsubst %.c, %, $(SRCFILES))


all: $(OBJS)

%: %.c
	gcc -Wall -g3  $< -L.. -lqratpreplus -o $@

clean:
	rm -f $(OBJS) *~
